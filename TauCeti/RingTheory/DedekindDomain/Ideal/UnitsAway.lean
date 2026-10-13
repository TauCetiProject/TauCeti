/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.Ideal.Away
public import TauCeti.RingTheory.DedekindDomain.SInteger.Unit
public import TauCeti.RingTheory.ClassGroup.Basic

/-!
# Local units and principal ideals away from finitely many primes

For a Dedekind domain `R` with fraction field `K`, the nonzero field elements having valuation
one at each prime of a finite set `S` are Mathlib's `Sᶜ`-units. These elements need not be units
of `R`, or even integral at primes outside `S`.

`principalIdealAway` restricts Mathlib's principal-ideal map to this existing carrier, taking
values in `idealsAway K S`. Its range is exactly the kernel of the ordinary class map on
ideals away from `S`. This is the principal-ideal part of the ray-class exact sequence, before
imposing multiplicative congruences or real-place signs.

A principal fractional ideal has multiplicity zero at a prime exactly when its generator has
valuation one there. `toPrincipalIdeal_mem_idealsAway_iff` applies this criterion at every prime
of `S`, identifying the generators whose principal ideals lie in `idealsAway K S`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors

namespace TauCeti.NumberFieldArithmetic

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A principal fractional ideal is away from `S` exactly when its generator is an `Sᶜ`-unit,
that is, a local unit at every prime of `S`. -/
theorem toPrincipalIdeal_mem_idealsAway_iff {S : Finset (HeightOneSpectrum R)} {x : Kˣ} :
    toPrincipalIdeal R K x ∈ idealsAway K S ↔ x ∈ (S : Set (HeightOneSpectrum R))ᶜ.unit K := by
  rw [mem_idealsAway_iff, Set.mem_unit_iff]
  simp only [Set.mem_compl_iff, Finset.mem_coe, not_not]
  refine forall_congr' fun v ↦ forall_congr' fun _ ↦ ?_
  rw [FractionalIdeal.count_toPrincipalIdeal_eq_neg_log_valuation, neg_eq_zero]
  constructor
  · intro h
    have hne : v.valuation K (x : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
    rw [← WithZero.exp_log hne, h, WithZero.exp_zero]
  · intro h
    rw [h, WithZero.log_one]

variable (K) in
/-- The principal-ideal map on `Sᶜ`-units, taking values in the fractional ideals away from `S`.
The domain records the local-unit condition at every prime of `S`. -/
noncomputable def principalIdealAway (S : Finset (HeightOneSpectrum R)) :
    (S : Set (HeightOneSpectrum R))ᶜ.unit K →* idealsAway K S :=
  ((toPrincipalIdeal R K).comp ((S : Set (HeightOneSpectrum R))ᶜ.unit K).subtype).codRestrict _
    fun x ↦ toPrincipalIdeal_mem_idealsAway_iff.mpr x.2

/-- The restricted principal-ideal map does not change the underlying principal ideal. -/
@[simp]
theorem coe_principalIdealAway (S : Finset (HeightOneSpectrum R))
    (x : (S : Set (HeightOneSpectrum R))ᶜ.unit K) :
    (principalIdealAway K S x : (FractionalIdeal R⁰ K)ˣ) = toPrincipalIdeal R K (x : Kˣ) :=
  (rfl)

/-- The principal ideals away from `S` are exactly the kernel of the ordinary class map. -/
theorem range_principalIdealAway (S : Finset (HeightOneSpectrum R)) :
    (principalIdealAway K S).range =
      ((ClassGroup.mk K).comp (idealsAway K S).subtype).ker := by
  ext I
  rw [MonoidHom.mem_range, MonoidHom.mem_ker, MonoidHom.comp_apply,
    Subgroup.subtype_apply, ClassGroup.mk_eq_one_iff_exists]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, coe_principalIdealAway S x⟩
  · rintro ⟨x, hx⟩
    refine ⟨⟨x, toPrincipalIdeal_mem_idealsAway_iff.mp (hx ▸ I.2)⟩, ?_⟩
    exact Subtype.ext ((coe_principalIdealAway S _).trans hx)

end TauCeti.NumberFieldArithmetic
