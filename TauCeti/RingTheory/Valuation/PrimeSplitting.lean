/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# The prime-splitting square of a valuation ring

Let `V` be a valuation domain and `p` a prime ideal of `V`. Then `V ⧸ p` and the localization
`V_p` are again valuation domains, the map `p → p V_p` is an isomorphism of `V`-modules, and the
square of rings
```
V   ⟶ V ⧸ p
↓       ↓
V_p ⟶ κ(p)
```
is cartesian. The square glues `V` from the two valuation rings `V ⧸ p` and `V_p`, whose spectra
are the two halves of `Spec V` cut at `p`, along their common point `κ(p)`; since `p ≅ p V_p`, the
map `V → V_p` together with the ideal `p` is a Milnor square. This is the basic step for
decomposing a valuation ring along a chain of primes, as in the theory of arc-descent.

The underlying fact is elementary: if `x ∈ p` and `s ∉ p`, then `s` divides `x`, and the quotient
`x / s` again lies in `p`. Most of this holds for any `PreValuationRing`, with no domain
hypothesis.

## Main results

* `TauCeti.PreValuationRing.dvd_of_mem_of_notMem`: an element outside an ideal divides every
  element of the ideal.
* `TauCeti.PreValuationRing.of_isLocalization` and `TauCeti.ValuationRing.of_isLocalization`:
  localizations of (pre)valuation rings are (pre)valuation rings. There are instances for
  `Localization M` and for quotients `R ⧸ I`.
* `TauCeti.PreValuationRing.exists_mem_algebraMap_eq_of_mem_map`: every element of `p S`, for a
  localization `S` at a submonoid avoiding `p`, is the image of an element of `p`.
* `TauCeti.ValuationRing.primeEquivMap`: the `V`-linear isomorphism `p ≃ p V_p`.
* `TauCeti.ValuationRing.isPullback_quotient_localizationAtPrime`: the square
  `V, V ⧸ p, V_p, κ(p)` is a pullback square of commutative rings.

## References

* B. Bhatt, A. Mathew, *The arc-topology*, Cambridge J. Math. 9 (2021), Proposition 2.8.
-/

public section

open CategoryTheory

namespace TauCeti

namespace PreValuationRing

section CommSemiring

variable {R : Type*} [CommSemiring R] [PreValuationRing R]

/-- In a ring with total divisibility, an element outside an ideal divides every element of the
ideal. -/
theorem dvd_of_mem_of_notMem {I : Ideal R} {x s : R} (hx : x ∈ I) (hs : s ∉ I) : s ∣ x :=
  (ValuationRing.dvd_total s x).resolve_right fun h ↦ hs (I.mem_of_dvd h hx)

/-- In a ring with total divisibility, an element `x` of a prime ideal `p` is divisible by every
`s ∉ p`, with quotient again in `p`. -/
theorem exists_mem_mul_eq_of_mem_of_notMem {p : Ideal R} [p.IsPrime] {x s : R} (hx : x ∈ p)
    (hs : s ∉ p) : ∃ y ∈ p, s * y = x := by
  obtain ⟨y, rfl⟩ := dvd_of_mem_of_notMem hx hs
  exact ⟨y, (Ideal.IsPrime.mem_or_mem ‹_› hx).resolve_left hs, rfl⟩

/-- A localization of a ring with total divisibility has total divisibility. -/
theorem of_isLocalization (M : Submonoid R) (S : Type*) [CommSemiring S] [Algebra R S]
    [IsLocalization M S] : PreValuationRing S := by
  refine PreValuationRing.iff_dvd_total.mpr ⟨fun x y ↦ ?_⟩
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M x
  obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective M y
  -- If `a * c = b` then `a / s * (s * c / t) = b / t`, and symmetrically.
  rcases ValuationRing.dvd_total a b with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · refine .inl ⟨IsLocalization.mk' S (s * c : R) t, ?_⟩
    rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq, Submonoid.coe_mul]
    congr 1
    ring
  · refine .inr ⟨IsLocalization.mk' S (t * c : R) s, ?_⟩
    rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq, Submonoid.coe_mul]
    congr 1
    ring

/-- `Localization M` of a ring with total divisibility has total divisibility. -/
instance (M : Submonoid R) : PreValuationRing (Localization M) :=
  of_isLocalization M _

/-- Let `S` be a localization of a ring with total divisibility at a submonoid `M` avoiding a
prime ideal `p`. Then every element of the extended ideal `p S` is the image of an element
of `p`. -/
theorem exists_mem_algebraMap_eq_of_mem_map {p : Ideal R} [p.IsPrime] {M : Submonoid R}
    (hM : M ≤ p.primeCompl) {S : Type*} [CommSemiring S] [Algebra R S] [IsLocalization M S]
    {z : S} (hz : z ∈ p.map (algebraMap R S)) : ∃ x ∈ p, algebraMap R S x = z := by
  obtain ⟨⟨⟨x, hx⟩, s⟩, h⟩ := (IsLocalization.mem_map_algebraMap_iff M S).mp hz
  obtain ⟨y, hy, rfl⟩ := exists_mem_mul_eq_of_mem_of_notMem hx (hM s.property)
  refine ⟨y, hy, ?_⟩
  rw [map_mul, mul_comm] at h
  exact ((IsLocalization.map_units S s).mul_right_injective h).symm

end CommSemiring

/-- A quotient of a ring with total divisibility has total divisibility. -/
instance {R : Type*} [CommRing R] [PreValuationRing R] (I : Ideal R) :
    PreValuationRing (R ⧸ I) :=
  Function.Surjective.preValuationRing (Ideal.Quotient.mk I).toMonoidHom.toMulHom
    Ideal.Quotient.mk_surjective

end PreValuationRing

namespace ValuationRing

/-- A localization of a ring with total divisibility is a valuation ring as soon as it is a
domain. For a valuation domain this applies to every localization at a submonoid not
containing `0`. -/
theorem of_isLocalization {R : Type*} [CommRing R] [PreValuationRing R] (M : Submonoid R)
    (S : Type*) [CommRing S] [IsDomain S] [Algebra R S] [IsLocalization M S] :
    ValuationRing S :=
  have := PreValuationRing.of_isLocalization M S
  {}

/-- `Localization M` of a ring with total divisibility is a valuation ring when it is a domain;
for instance `Localization.AtPrime p` for a prime `p` of a valuation domain. -/
instance {R : Type*} [CommRing R] [PreValuationRing R] (M : Submonoid R)
    [IsDomain (Localization M)] : ValuationRing (Localization M) where

/-- A quotient of a ring with total divisibility is a valuation ring when it is a domain;
for instance `R ⧸ p` for a prime `p` of a valuation domain `R`. -/
instance {R : Type*} [CommRing R] [PreValuationRing R] (I : Ideal R) [IsDomain (R ⧸ I)] :
    ValuationRing (R ⧸ I) where

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]

section primeEquivMap

variable (p : Ideal R) [p.IsPrime] (S : Type*) [CommRing S] [Algebra R S]
  [IsLocalization.AtPrime S p]

/-- For a prime `p` of a valuation domain `R` and the localization `S = R_p`, the map
`p → p S` is an isomorphism of `R`-modules. -/
noncomputable def primeEquivMap : p ≃ₗ[R] (p.map (algebraMap R S)).restrictScalars R :=
  LinearEquiv.ofBijective
    ((Algebra.linearMap R S).restrict fun _ hx ↦ Ideal.mem_map_of_mem _ hx)
    ⟨fun _ _ h ↦ Subtype.ext <|
        IsLocalization.injective S p.primeCompl_le_nonZeroDivisors congr(($h : S)),
      fun ⟨_, hz⟩ ↦
        have ⟨x, hx, hxz⟩ := PreValuationRing.exists_mem_algebraMap_eq_of_mem_map le_rfl hz
        ⟨⟨x, hx⟩, Subtype.ext hxz⟩⟩

/-- `primeEquivMap` is the restriction of `algebraMap R S`. -/
@[simp]
theorem coe_primeEquivMap_apply (x : p) : (primeEquivMap p S x : S) = algebraMap R S x :=
  (rfl)

/-- The inverse of `primeEquivMap` picks the preimage under `algebraMap R S`. -/
@[simp]
theorem algebraMap_primeEquivMap_symm_apply (z : (p.map (algebraMap R S)).restrictScalars R) :
    algebraMap R S ((primeEquivMap p S).symm z : R) = z := by
  rw [← coe_primeEquivMap_apply, LinearEquiv.apply_symm_apply]

end primeEquivMap

variable {p : Ideal R} [p.IsPrime]

/-- Elements of `R ⧸ p` and of `R_p` with the same image in the residue field `κ(p)` come from a
common element of the valuation domain `R`. -/
theorem exists_mk_eq_and_algebraMap_eq {a : R ⧸ p} {b : Localization.AtPrime p}
    (h : algebraMap (R ⧸ p) p.ResidueField a = algebraMap _ p.ResidueField b) :
    ∃ x : R, Ideal.Quotient.mk p x = a ∧ algebraMap R (Localization.AtPrime p) x = b := by
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hmem : b - algebraMap R _ u ∈ p.map (algebraMap R (Localization.AtPrime p)) := by
    rw [Localization.AtPrime.map_eq_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, map_sub,
      sub_eq_zero, ← IsLocalRing.ResidueField.algebraMap_eq, ← h,
      Ideal.algebraMap_quotient_residueField_mk,
      IsScalarTower.algebraMap_apply R (Localization.AtPrime p) p.ResidueField]
  obtain ⟨y, hy, hyb⟩ := PreValuationRing.exists_mem_algebraMap_eq_of_mem_map le_rfl hmem
  refine ⟨u + y, ?_, ?_⟩
  · rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hy, add_zero]
  · rw [map_add, hyb, add_sub_cancel]

/-- **The prime-splitting square.** For a prime `p` of a valuation domain `R`, the square
`R → R ⧸ p → κ(p)`, `R → R_p → κ(p)` is a pullback square of commutative rings. -/
theorem isPullback_quotient_localizationAtPrime :
    IsPullback (CommRingCat.ofHom (Ideal.Quotient.mk p))
      (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p)))
      (CommRingCat.ofHom (algebraMap (R ⧸ p) p.ResidueField))
      (CommRingCat.ofHom (algebraMap (Localization.AtPrime p) p.ResidueField)) := by
  refine IsPullback.of_map_of_faithful (forget CommRingCat) ?_
  rw [Limits.Types.isPullback_iff]
  refine ⟨?_, fun x y ⟨_, h⟩ ↦ ?_, fun a b h ↦ ?_⟩
  · ext x
    simpa using IsScalarTower.algebraMap_apply R (Localization.AtPrime p) p.ResidueField x
  · simpa using h
  · simpa using exists_mk_eq_and_algebraMap_eq (by simpa using h)

end ValuationRing

end TauCeti
