/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import TauCeti.RingTheory.FractionalIdeal.Operations

/-!
# Complements on the ideal class group

Facts about Mathlib's `ClassGroup R` and its principal-ideal map that Mathlib's own file does
not carry: the generator form of triviality of a class, that a principal fractional ideal has
trivial class, and the class `[v]` of a height one prime.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.classGroupMk`: the class `[v]` of a height one prime of a
  Dedekind domain.

## Main results

* `ClassGroup.mk_eq_one_iff_exists`: a class is trivial exactly when some `x : Kˣ` generates it.
  This is Mathlib's `ClassGroup.mk_eq_one_iff` with `Submodule.IsPrincipal` traded for the range
  of `toPrincipalIdeal`, which is the form a consumer that wants to *name* the generator can use.
* `ClassGroup.mk_toPrincipalIdeal`: a principal fractional ideal has trivial class. This is the
  `simp` form of `ClassGroup.mk_eq_one_iff` for the one witness that arises in practice, and it
  holds over any domain.
* `ClassGroup.mk_mul_mk_eq_one_iff`: the product of the classes of two invertible fractional
  ideals is trivial if and only if their product is principal as an `R`-submodule of `K`.
* `ClassGroup.mk_num`: an invertible fractional ideal and its integral numerator have the
  same class, over any domain and any choice of fraction field.
* `FractionalIdeal.exists_mk0_eq_toPrincipalIdeal_natCast_mul`: over a Dedekind domain with finite
  quotients and a characteristic-zero fraction field `K`, every invertible fractional ideal `I` can
  be scaled by a nonzero natural number `m` into a nonzero integral ideal `J` with `J = (m) * I`.
* `ClassGroup.isPrincipal_mul_iff_of_mk0_eq`: if a nonzero integral ideal `J` and an invertible
  fractional ideal `I` share the same class in `ClassGroup R`, then `𝔟 * J` is principal if and
  only if `𝔟 * I` is principal.
* `TauCeti.isPrincipalIdealRing_iff_subsingleton_classGroup`: a Dedekind domain is a principal
  ideal ring exactly when its class group is trivial, with no finiteness of the class group
  assumed.
* `IsDedekindDomain.HeightOneSpectrum.classGroupMk_eq_mk0`: the defining formula for `[v]`, as
  `ClassGroup.mk0` of `v.asIdeal`. This needs no fraction field.
* `IsDedekindDomain.HeightOneSpectrum.classGroupMk_eq_mk`: `[v]` is the class of `v.asIdeal` seen
  as an invertible fractional ideal of any fraction field `K`.
* `Ideal.isPrincipal_pow_natCard_classGroup`: if the class group is finite, `I ^ h` is principal
  for every ideal `I`, where `h` is the order of the class group.
* `ClassGroup.mk0_eq_inv_mk_iff`: a nonzero ideal `J` has class `[I]⁻¹` exactly when `J * I` is
  principal, with the generator delivered as a unit of `K`.

The class-triviality and numerator results use `[IsDomain R]`, since none of them is
Dedekind-specific. None of them needs the factorization of a fractional ideal into primes, so this
file does not import it; the results that do live in
`TauCeti.RingTheory.ClassGroup.HeightOneSpectrum`, which every consumer of *those* pays for and
consumers of these do not.

Split out of material adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/FractionalIdeal.lean`
at revision `66889eada51a`, Apache 2.0, by Michael Stoll). Following this repository's
convention for adapted material, the upstream authorship is credited here rather than in the
copyright header.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors

/-- A unit fractional ideal has trivial class exactly when it is principal, with the generator
delivered as a unit of `K`. This is Mathlib's `ClassGroup.mk_eq_one_iff` with
`Submodule.IsPrincipal` traded for the range of `toPrincipalIdeal`, which is the form a consumer
that wants to *name* the generator can use. -/
lemma ClassGroup.mk_eq_one_iff_exists {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] {I : (FractionalIdeal R⁰ K)ˣ} :
    ClassGroup.mk K I = 1 ↔ ∃ x : Kˣ, toPrincipalIdeal R K x = I := by
  rw [ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff, ← MonoidHom.mem_range,
    mem_principal_ideals_iff]
  exact exists_congr fun _ ↦ eq_comm

/-- A principal fractional ideal has trivial ideal class. -/
@[simp]
lemma ClassGroup.mk_toPrincipalIdeal {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] (x : Kˣ) :
    ClassGroup.mk K (toPrincipalIdeal R K x) = 1 :=
  ClassGroup.mk_eq_one_iff_exists.mpr ⟨x, rfl⟩

/-- The product of the ideal classes of two invertible fractional ideals is trivial if and only if
their product is principal as an `R`-submodule of `K`. -/
theorem ClassGroup.mk_mul_mk_eq_one_iff {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] {I J : (FractionalIdeal R⁰ K)ˣ} :
    ClassGroup.mk K I * ClassGroup.mk K J = 1 ↔
      Submodule.IsPrincipal ((I : FractionalIdeal R⁰ K) * (J : FractionalIdeal R⁰ K) :
        Submodule R K) := by
  rw [← map_mul, ClassGroup.mk_eq_one_iff, Units.val_mul, FractionalIdeal.coeToSubmodule_mul]

-- Extracted from the point-to-class surjectivity argument, adapted from Chris Birkbeck's
-- AINTLIB (`github.com/CBirkbeck/AINTLIB`), `HasseWeil/Pic0/ToClassSurjective.lean`
-- (`dev/hasse-weil @ 513e83879e2f`, Apache-2.0).
/-- Replacing an invertible fractional ideal by its integral numerator does not change its ideal
class. -/
@[simp]
theorem ClassGroup.mk_num {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] (I : (FractionalIdeal R⁰ K)ˣ) :
    let hnum : IsUnit (I.val.num : FractionalIdeal R⁰ K) :=
      FractionalIdeal.isUnit_num_iff.mpr I.isUnit
    ClassGroup.mk K hnum.unit = ClassGroup.mk K I := by
  dsimp only
  let u : Kˣ := (IsLocalization.map_units K I.val.den).unit
  have hnum : (FractionalIdeal.isUnit_num_iff.mpr I.isUnit).unit =
      toPrincipalIdeal R K u * I := by
    apply Units.ext
    simp only [IsUnit.unit_spec, Units.val_mul, coe_toPrincipalIdeal, u]
    exact (FractionalIdeal.den_mul_self_eq_num' R⁰ K I.val).symm
  rw [hnum, map_mul, ClassGroup.mk_toPrincipalIdeal, one_mul]

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- For every invertible fractional ideal `I` of a Dedekind domain with finite quotients and
characteristic-zero fraction field `K`, there exist a nonzero `m : ℕ` and a nonzero integral ideal
`J` such that `J = (m) * I`. -/
theorem FractionalIdeal.exists_mk0_eq_toPrincipalIdeal_natCast_mul [Ring.HasFiniteQuotients R]
    {K : Type*} [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
    (I : (FractionalIdeal R⁰ K)ˣ) :
    ∃ (m : ℕ) (hm : m ≠ 0) (J : (Ideal R)⁰),
      FractionalIdeal.mk0 K J =
        toPrincipalIdeal R K (Units.mk0 (m : K) (Nat.cast_ne_zero.mpr hm)) * I := by
  set d : R⁰ := (I : FractionalIdeal R⁰ K).den
  have hfin : Finite (R ⧸ Ideal.span {(d : R)}) :=
    Ring.HasFiniteQuotients.finiteQuotient
      (Ideal.span_singleton_eq_bot.not.mpr (nonZeroDivisors.coe_ne_zero d))
  set m : ℕ := Nat.card (R ⧸ Ideal.span {(d : R)})
  have hm : m ≠ 0 := Nat.card_pos.ne'
  have hm_mem : (m : R) ∈ Ideal.span {(d : R)} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← nsmul_one]
    exact card_nsmul_eq_zero'
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hm_mem
  have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hm_eq : (m : K) = algebraMap R K q * algebraMap R K (d : R) := by
    rw [← map_mul, mul_comm, ← hq, map_natCast]
  have hmul : FractionalIdeal.spanSingleton R⁰ (m : K) * (I : FractionalIdeal R⁰ K) =
      ((Ideal.span {q} * (I : FractionalIdeal R⁰ K).num : Ideal R) : FractionalIdeal R⁰ K) := by
    rw [hm_eq, map_mul (FractionalIdeal.spanSingleton R⁰), mul_assoc,
      FractionalIdeal.den_mul_self_eq_num', ← FractionalIdeal.coeIdeal_span_singleton,
      ← FractionalIdeal.coeIdeal_mul]
  have hJ0 : Ideal.span {q} * (I : FractionalIdeal R⁰ K).num ≠ 0 := fun h0 ↦
    mul_ne_zero (FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hmK) I.ne_zero
      (by simp [hmul, h0])
  refine ⟨m, hm, ⟨Ideal.span {q} * (I : FractionalIdeal R⁰ K).num,
    mem_nonZeroDivisors_of_ne_zero hJ0⟩, Units.ext ?_⟩
  rw [FractionalIdeal.coe_mk0, Units.val_mul, coe_toPrincipalIdeal, Units.val_mk0, hmul]

/-- If a nonzero integral ideal `J` and an invertible fractional ideal `I` have the same class in
`ClassGroup R`, then a nonzero integral ideal `𝔟` has principal product `𝔟 * J` if and only if
`𝔟 * I` is principal as an `R`-submodule of `K`. -/
theorem ClassGroup.isPrincipal_mul_iff_of_mk0_eq {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] {I : (FractionalIdeal R⁰ K)ˣ} {J : (Ideal R)⁰}
    (hJ : ClassGroup.mk0 J = ClassGroup.mk K I) (𝔟 : (Ideal R)⁰) :
    Submodule.IsPrincipal ((𝔟 : Ideal R) * (J : Ideal R)) ↔
      Submodule.IsPrincipal (((𝔟 : Ideal R) : FractionalIdeal R⁰ K) *
        (I : FractionalIdeal R⁰ K) : Submodule R K) := by
  have hclass : ClassGroup.mk0 (𝔟 * J) =
      ClassGroup.mk K (FractionalIdeal.mk0 K 𝔟) * ClassGroup.mk K I := by
    simp [hJ]
  rw [← Submonoid.coe_mul, ← ClassGroup.mk0_eq_one_iff (𝔟 * J).property, hclass,
    ClassGroup.mk_mul_mk_eq_one_iff]
  simp

/-- **A Dedekind domain is a principal ideal ring exactly when its class group is trivial.**
Mathlib's `card_classGroup_eq_one_iff` is the same statement with the class number, and needs a
`Fintype` instance on the class group that this form does not ask for. -/
theorem TauCeti.isPrincipalIdealRing_iff_subsingleton_classGroup :
    IsPrincipalIdealRing R ↔ Subsingleton (ClassGroup R) := by
  refine ⟨fun _ ↦ Fintype.card_le_one_iff_subsingleton.mp (card_classGroup_eq_one (R := R)).le,
    fun _ ↦ ?_⟩
  have := Fintype.ofFinite (ClassGroup R)
  exact card_classGroup_eq_one_iff.mp
    (Fintype.card_eq_one_iff.mpr ⟨1, fun _ ↦ Subsingleton.elim _ _⟩)

/-- The class of a height one prime `v` in the ideal class group of `R`. -/
noncomputable def IsDedekindDomain.HeightOneSpectrum.classGroupMk (v : HeightOneSpectrum R) :
    ClassGroup R :=
  ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩

-- Deliberately not `@[simp]`: the statements that matter here are phrased in the folded form,
-- and in `HeightOneSpectrum.classGroupMk '' T` the occurrence is unapplied, so `simp` could not
-- unfold it there anyway — tagging this would only leave goals in mixed normal forms.
/-- The class of `v` is the class of the nonzero ideal `v.asIdeal`. -/
lemma IsDedekindDomain.HeightOneSpectrum.classGroupMk_eq_mk0 (v : HeightOneSpectrum R) :
    v.classGroupMk = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  -- Not `rfl`: a `public section` leaves the body of `classGroupMk` unexposed, so the equation
  -- has to come from the definition's own equation lemma.
  simp only [IsDedekindDomain.HeightOneSpectrum.classGroupMk]

/-- The class of `v` is the class of `v.asIdeal` viewed as an invertible fractional ideal of a
fraction field `K`. -/
lemma IsDedekindDomain.HeightOneSpectrum.classGroupMk_eq_mk (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) :
    v.classGroupMk = ClassGroup.mk K (Units.mk0 (v.asIdeal : FractionalIdeal R⁰ K)
      (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)) := by
  rw [classGroupMk_eq_mk0, ← ClassGroup.mk_mk0 K]
  exact congrArg _ (Units.ext (FractionalIdeal.coe_mk0 K _))

/-- If the class group of `R` is finite, the power of any ideal by the order of the class group
is principal. -/
lemma Ideal.isPrincipal_pow_natCard_classGroup [Finite (ClassGroup R)] (I : Ideal R) :
    (I ^ Nat.card (ClassGroup R)).IsPrincipal := by
  rcases eq_or_ne I ⊥ with rfl | hI
  · rw [← Ideal.zero_eq_bot, zero_pow Nat.card_pos.ne']
    exact bot_isPrincipal
  have hI' : I ∈ (Ideal R)⁰ := mem_nonZeroDivisors_of_ne_zero hI
  rw [← ClassGroup.mk0_eq_one_iff (pow_mem hI' _)]
  have h1 : ClassGroup.mk0 ⟨I, hI'⟩ ^ Nat.card (ClassGroup R) = 1 := pow_card_eq_one'
  rwa [← map_pow, SubmonoidClass.mk_pow] at h1

/-- A nonzero ideal `J` lies in the inverse class `(ClassGroup.mk K I)⁻¹` exactly when `J * I` is
the principal fractional ideal generated by some `x : Kˣ`. -/
lemma ClassGroup.mk0_eq_inv_mk_iff {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (I : (FractionalIdeal R⁰ K)ˣ) (J : (Ideal R)⁰) :
    ClassGroup.mk0 J = (ClassGroup.mk K I)⁻¹ ↔
      ∃ x : Kˣ, (J : FractionalIdeal R⁰ K) * (I : FractionalIdeal R⁰ K) =
        FractionalIdeal.spanSingleton R⁰ (x : K) := by
  rw [eq_inv_iff_mul_eq_one, ← ClassGroup.mk_mk0 K, ← map_mul, ClassGroup.mk_eq_one_iff_exists]
  simp only [Units.ext_iff, Units.val_mul, FractionalIdeal.coe_mk0, coe_toPrincipalIdeal, eq_comm]

end
