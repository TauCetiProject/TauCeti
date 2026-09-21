/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.FrobeniusPrimeSet
import TauCeti.NumberTheory.NumberField.Frobenius.FiberCount
public import TauCeti.NumberTheory.NumberField.Frobenius.FixedField.Fiber

/-!
# Frobenius fibers over cyclic fixed fields

Let `L / K` be a finite Galois extension, let `C` be a conjugacy class in `Gal(L/K)`, and choose
`sigma` in `C`.  Put `E = L ^ <sigma>`.  This file counts the primes of `E` over a prime in the
Frobenius class `C` whose relative Frobenius in `L / E` is the automorphism induced by `sigma`:

```text
#G / (#C * orderOf sigma).
```

Contraction identifies these primes with the primes of `L` at which `sigma` itself is an
arithmetic Frobenius.  The latter form one orbit under the centralizer of `sigma`; its stabilizer
is `<sigma>`.  The resulting count is the fixed-field multiplicity used when transferring prime
sums and densities between `E` and `K`.

## Main result

* `NumberField.Chebotarev.fixedField_frobenius_fiber_eq_image`: contraction identifies the
  relative fiber with the image of the corresponding absolute Frobenius fiber.
* `NumberField.Chebotarev.inertiaDeg_eq_one_iff_under_mem_frobeniusPrimeSet`: away from the
  ramified primes, a prime of the relative fiber has residue degree one over `K` exactly when the
  prime below it lies in the Frobenius fiber of `sigma`.
* `NumberField.Chebotarev.fixedField_frobenius_fiber_card`: the exact cardinality of the relative
  Frobenius fiber over one prime of `K`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, Section 9.
* R. Sharifi, *Algebraic Number Theory*, Theorem 7.2.2.
* C. Birkbeck and R. Brasca,
  [*Chebotarev density*](https://github.com/CBirkbeck/chebotarev-density),
  `CebotarevDensity/FixedFieldDensity.lean` at commit
  `55a89985d47a3befcf6069aca1da250ff088b5c7` (Apache-2.0).
-/

public section

open IntermediateField
open scoped NumberField Pointwise
open IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

private theorem isArithFrobAt_of_fixedField_isArithFrobAt
    (sigma : L ≃ₐ[K] L) (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ frobeniusPrimeSet K L (ConjClasses.mk sigma))
    (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (hQp : Q.under (𝓞 K) = p.asIdeal)
    (hrel : IsArithFrobAt (𝓞 ↥(fixedField (Subgroup.zpowers sigma)))
      sigma.toFixedFieldAlgEquiv Q) :
    IsArithFrobAt (𝓞 K) sigma Q := by
  have hur : ∀ (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver p.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) P :=
    (mem_frobeniusPrimeSet_iff.mp hp).choose
  have : Q.LiesOver p.asIdeal := ⟨hQp.symm⟩
  let _ : Algebra.IsUnramifiedAt (𝓞 K) Q := hur Q
  obtain ⟨phi, hphi⟩ := NumberField.exists_isArithFrobAt K Q
    (Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot Q)
  have hclass : ConjClasses.mk phi = ConjClasses.mk sigma := by
    rw [← (mem_frobeniusPrimeSet_iff.mp hp).choose_spec]
    exact (artinSymbol_eq_mk_of_isArithFrobAt p.asIdeal hur Q phi hphi).symm
  have hconj : IsConj sigma phi :=
    ConjClasses.mk_eq_mk_iff_isConj.mp hclass.symm
  have hsigma_mem : sigma ∈ Subgroup.zpowers phi := by
    rw [Ideal.zpowers_eq_stabilizer_of_isArithFrobAt Q hphi.ne_bot hphi]
    rw [MulAction.mem_stabilizer_iff, ← AlgEquiv.toFixedFieldAlgEquiv_smul_ideal]
    exact hrel.mem_stabilizer
  have horder : orderOf sigma = orderOf phi :=
    SemiconjBy.orderOf_eq (↑hconj.choose) hconj.choose_spec
  have hz : Subgroup.zpowers sigma = Subgroup.zpowers phi := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hsigma_mem)
    rw [Nat.card_zpowers, Nat.card_zpowers, horder]
  have hdeg : (Q.under (𝓞 ↥(fixedField (Subgroup.zpowers sigma)))).inertiaDeg (𝓞 K) = 1 :=
    (Ideal.inertiaDeg_under_fixedField_eq_one_iff Q hphi.ne_bot
      (Subgroup.zpowers sigma) hphi).2 (hz.symm ▸ Subgroup.mem_zpowers phi)
  have habs := NumberField.isArithFrobAt_restrictScalars_of_inertiaDeg_eq_one hrel hdeg
  rw [AlgEquiv.restrictScalars_toFixedFieldAlgEquiv] at habs
  exact habs

/-- **Contraction identifies the fixed-field and absolute Frobenius fibers.** Over a prime `p`
with Artin class represented by `sigma`, contraction from `L` to `L ^ <sigma>` carries exactly the
primes whose absolute Frobenius is `sigma` onto the primes whose relative Artin class is represented
by `sigma.toFixedFieldAlgEquiv`. -/
theorem fixedField_frobenius_fiber_eq_image
    (sigma : L ≃ₐ[K] L) (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ frobeniusPrimeSet K L (ConjClasses.mk sigma)) :
    {P : HeightOneSpectrum (𝓞 ↥(fixedField (Subgroup.zpowers sigma))) |
        P.under (𝓞 K) = p ∧
          P ∈ frobeniusPrimeSet ↥(fixedField (Subgroup.zpowers sigma)) L
            (ConjClasses.mk sigma.toFixedFieldAlgEquiv)} =
      (fun Q : HeightOneSpectrum (𝓞 L) ↦
        Q.under (𝓞 ↥(fixedField (Subgroup.zpowers sigma)))) ''
        {Q : HeightOneSpectrum (𝓞 L) |
          Q.under (𝓞 K) = p ∧ IsArithFrobAt (𝓞 K) sigma Q.asIdeal} := by
  ext P
  constructor
  · rintro ⟨hPp, hP⟩
    obtain ⟨Q, hQ⟩ := exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk hP
    have hQne : Q.1 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot P.ne_bot Q.1
    let Q' : HeightOneSpectrum (𝓞 L) := HeightOneSpectrum.ofPrime
      (Ideal.prime_of_isPrime hQne inferInstance)
    have hQE : Q'.under (𝓞 ↥(fixedField (Subgroup.zpowers sigma))) = P := by
      apply HeightOneSpectrum.ext
      exact Q.2.2.over.symm
    have hQK' : Q.1.under (𝓞 K) = p.asIdeal := by
      calc
        Q.1.under (𝓞 K) =
            (Q.1.under (𝓞 ↥(fixedField (Subgroup.zpowers sigma)))).under (𝓞 K) :=
          (Ideal.under_under (B := 𝓞 ↥(fixedField (Subgroup.zpowers sigma))) Q.1).symm
        _ = P.asIdeal.under (𝓞 K) := congrArg (Ideal.under (𝓞 K)) Q.2.2.over.symm
        _ = p.asIdeal := (HeightOneSpectrum.under_asIdeal (𝓞 K) P).symm.trans
          (congrArg HeightOneSpectrum.asIdeal hPp)
    have hQK : Q'.under (𝓞 K) = p := HeightOneSpectrum.ext hQK'
    have habs : IsArithFrobAt (𝓞 K) sigma Q.1 :=
      isArithFrobAt_of_fixedField_isArithFrobAt sigma p hp Q.1 hQK' hQ
    exact ⟨Q', ⟨hQK, habs⟩, hQE⟩
  · rintro ⟨Q, ⟨hQp, hQ⟩, rfl⟩
    have hur : ∀ (R : Ideal (𝓞 L)) [R.IsPrime] [R.LiesOver p.asIdeal],
        Algebra.IsUnramifiedAt (𝓞 K) R :=
      (mem_frobeniusPrimeSet_iff.mp hp).choose
    have : Q.asIdeal.LiesOver p.asIdeal :=
      ⟨(congrArg HeightOneSpectrum.asIdeal hQp).symm⟩
    let _ : Algebra.IsUnramifiedAt (𝓞 K) Q.asIdeal := hur Q.asIdeal
    obtain ⟨tau, htau, hres⟩ := Ideal.exists_isArithFrobAt_and_restrictScalars_eq Q.asIdeal sigma hQ
    have htau_eq : tau = sigma.toFixedFieldAlgEquiv :=
      AlgEquiv.restrictScalars_injective K
        (hres.trans sigma.restrictScalars_toFixedFieldAlgEquiv.symm)
    have hurE : ∀ (R : Ideal (𝓞 L)) [R.IsPrime]
        [R.LiesOver (Q.under (𝓞 ↥(fixedField (Subgroup.zpowers sigma)))).asIdeal],
        Algebra.IsUnramifiedAt (𝓞 ↥(fixedField (Subgroup.zpowers sigma))) R := by
      intro R _ _
      have hover : R.under (𝓞 K) = p.asIdeal := by
        calc
          R.under (𝓞 K) =
              (R.under (𝓞 ↥(fixedField (Subgroup.zpowers sigma)))).under (𝓞 K) :=
            (Ideal.under_under
              (B := 𝓞 ↥(fixedField (Subgroup.zpowers sigma))) R).symm
          _ = (Q.under (𝓞 ↥(fixedField (Subgroup.zpowers sigma)))).asIdeal.under (𝓞 K) :=
            congrArg (Ideal.under (𝓞 K)) Ideal.LiesOver.over.symm
          _ = Q.asIdeal.under (𝓞 K) :=
            (Ideal.under_under (B := 𝓞 ↥(fixedField (Subgroup.zpowers sigma))) Q.asIdeal)
          _ = p.asIdeal := (HeightOneSpectrum.under_asIdeal (𝓞 K) Q).symm.trans
            (congrArg HeightOneSpectrum.asIdeal hQp)
      have : R.LiesOver p.asIdeal := ⟨hover.symm⟩
      exact Algebra.IsUnramifiedAt.of_restrictScalars (𝓞 K) R
    have : Q.asIdeal.LiesOver
        (Q.under (𝓞 ↥(fixedField (Subgroup.zpowers sigma)))).asIdeal :=
      ⟨HeightOneSpectrum.under_asIdeal _ Q⟩
    refine ⟨?_, mem_frobeniusPrimeSet_mk_of_isArithFrobAt hurE Q.asIdeal (htau_eq ▸ htau)⟩
    apply HeightOneSpectrum.ext
    simpa only [HeightOneSpectrum.under_asIdeal, Ideal.under_under] using
      congrArg HeightOneSpectrum.asIdeal hQp

/-- **Residue degree one detects the absolute Frobenius class below a relative fiber.** Let `P`
be a prime of `L ^ <sigma>` whose relative Artin class in `L / L ^ <sigma>` is represented by
`sigma.toFixedFieldAlgEquiv`, and suppose that the prime of `K` below `P` is unramified in `L`.
Then `P` has residue degree one over `K` exactly when the prime below it has Artin class `[sigma]`.

Membership of `P` in the relative fiber does not by itself fix the class below.  If `L / K` is
cyclic of degree four with generator `g` and `sigma = g ^ 2`, a prime of `K` with Frobenius `g` is
inert in `L ^ <g ^ 2>`, and the prime above it has relative Frobenius `g ^ 2`.

The unramifiedness hypothesis cannot be dropped.  For `K = ℚ`, `L = ℚ(∛2, ζ₃)` and `sigma` a
transposition, the prime `𝔓` of `ℚ(∛2)` above `2` has residue degree one and relative Frobenius
`sigma`, although `2` ramifies in `L` and so has no Artin class.

Conversely, a prime of `K` in the class of `sigma` can have primes of residue degree one above it
whose relative Frobenius is another generator of `<sigma>`; `fixedField_frobenius_fiber_card`
counts those whose relative Frobenius is `sigma`. -/
theorem inertiaDeg_eq_one_iff_under_mem_frobeniusPrimeSet (sigma : L ≃ₐ[K] L)
    {P : HeightOneSpectrum (𝓞 ↥(fixedField (Subgroup.zpowers sigma)))}
    (hP : P ∈ frobeniusPrimeSet ↥(fixedField (Subgroup.zpowers sigma)) L
      (ConjClasses.mk sigma.toFixedFieldAlgEquiv))
    (hram : P.under (𝓞 K) ∉ ramifiedPrimes K L) :
    P.asIdeal.inertiaDeg (𝓞 K) = 1 ↔
      P.under (𝓞 K) ∈ frobeniusPrimeSet K L (ConjClasses.mk sigma) := by
  obtain ⟨Q, hQ⟩ := exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk hP
  have hQE : Q.1.under (𝓞 ↥(fixedField (Subgroup.zpowers sigma))) = P.asIdeal :=
    Q.2.2.over.symm
  have hQK : Q.1.under (𝓞 K) = (P.under (𝓞 K)).asIdeal := by
    rw [HeightOneSpectrum.under_asIdeal]
    exact (Ideal.under_under (B := 𝓞 ↥(fixedField (Subgroup.zpowers sigma))) Q.1).symm.trans
      (congrArg (Ideal.under (𝓞 K)) hQE)
  have : Q.1.LiesOver (P.under (𝓞 K)).asIdeal := ⟨hQK.symm⟩
  constructor
  · intro hdeg
    rw [mem_ramifiedPrimes_iff, not_not] at hram
    have habs := NumberField.isArithFrobAt_restrictScalars_of_inertiaDeg_eq_one hQ
      (hQE ▸ hdeg)
    rw [AlgEquiv.restrictScalars_toFixedFieldAlgEquiv] at habs
    exact mem_frobeniusPrimeSet_mk_of_isArithFrobAt hram Q.1 habs
  · intro hp
    let _ : Algebra.IsUnramifiedAt (𝓞 K) Q.1 := isUnramifiedAt_of_mem_frobeniusPrimeSet hp Q.1
    have habs := isArithFrobAt_of_fixedField_isArithFrobAt sigma _ hp Q.1 hQK hQ
    rw [← hQE]
    exact Ideal.inertiaDeg_under_fixedField_eq_one_of_isArithFrobAt Q.1 habs.ne_bot habs

omit [IsGalois K L] in
private theorem under_fixedField_injOn_frobenius
    (sigma : L ≃ₐ[K] L) (p : HeightOneSpectrum (𝓞 K)) :
    Set.InjOn (fun Q : HeightOneSpectrum (𝓞 L) ↦
      Q.under (𝓞 ↥(fixedField (Subgroup.zpowers sigma))))
      {Q : HeightOneSpectrum (𝓞 L) |
        Q.under (𝓞 K) = p ∧ IsArithFrobAt (𝓞 K) sigma Q.asIdeal} := by
  intro Q hQ R hR hQR
  apply HeightOneSpectrum.ext
  let _ : R.asIdeal.LiesOver
      (Q.asIdeal.under (𝓞 ↥(fixedField (Subgroup.zpowers sigma)))) :=
    ⟨congrArg HeightOneSpectrum.asIdeal hQR⟩
  exact (Ideal.eq_of_smul_eq_of_liesOver_under_fixedField
    hQ.2.mem_stabilizer R.asIdeal).symm

-- The counting argument follows Birkbeck--Brasca, `CebotarevDensity/FixedFieldDensity.lean`.
/-- **The fixed-field Frobenius fiber count.** Let `sigma` represent the conjugacy class `C`, and
let `p` be an unramified prime with Artin class `C`.  The number of primes of
`L ^ <sigma>` above `p` whose relative Artin class in `L / L ^ <sigma>` is represented by
`sigma.toFixedFieldAlgEquiv` is

```text
#Gal(L/K) / (#C * orderOf sigma).
```

The division is exact by `ConjClasses.card_carrier_mul_orderOf_dvd`. -/
theorem fixedField_frobenius_fiber_card
    (C : ConjClasses (L ≃ₐ[K] L)) (sigma : L ≃ₐ[K] L) (hsigma : sigma ∈ C.carrier)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ frobeniusPrimeSet K L C) :
    Nat.card {P : HeightOneSpectrum (𝓞 ↥(fixedField (Subgroup.zpowers sigma))) //
      P.under (𝓞 K) = p ∧
        P ∈ frobeniusPrimeSet ↥(fixedField (Subgroup.zpowers sigma)) L
          (ConjClasses.mk sigma.toFixedFieldAlgEquiv)} =
      Nat.card (L ≃ₐ[K] L) / (Nat.card C.carrier * orderOf sigma) := by
  have hC : ConjClasses.mk sigma = C := ConjClasses.mem_carrier_iff_mk_eq.mp hsigma
  have hp' : p ∈ frobeniusPrimeSet K L (ConjClasses.mk sigma) := hC ▸ hp
  obtain ⟨Q, hQ⟩ := exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk hp'
  let _ : Algebra.IsUnramifiedAt (𝓞 K) Q.1 := isUnramifiedAt_of_mem_frobeniusPrimeSet hp Q.1
  let lowerFiber : Set (HeightOneSpectrum (𝓞 ↥(fixedField (Subgroup.zpowers sigma)))) :=
    {P | P.under (𝓞 K) = p ∧
      P ∈ frobeniusPrimeSet ↥(fixedField (Subgroup.zpowers sigma)) L
        (ConjClasses.mk sigma.toFixedFieldAlgEquiv)}
  let upperFiber : Set (HeightOneSpectrum (𝓞 L)) :=
    {R | R.under (𝓞 K) = p ∧ IsArithFrobAt (𝓞 K) sigma R.asIdeal}
  have himage : lowerFiber =
      (fun R : HeightOneSpectrum (𝓞 L) ↦
        R.under (𝓞 ↥(fixedField (Subgroup.zpowers sigma)))) '' upperFiber :=
    fixedField_frobenius_fiber_eq_image sigma p hp'
  have hinj := under_fixedField_injOn_frobenius sigma p
  have hupper : Nat.card upperFiber = Nat.card
      {R : Ideal (𝓞 L) // ∃ (_ : R.IsPrime) (_ : R.LiesOver p.asIdeal) (_ : R ≠ ⊥),
        IsArithFrobAt (𝓞 K) sigma R} :=
    Nat.card_congr (p.frobeniusFiberEquiv sigma)
  have hcount := Ideal.frobenius_fiber_card_mul_orderOf_eq_card_centralizer
    p.asIdeal Q.1 hQ
  have hupper_count : Nat.card upperFiber =
      Nat.card (Subgroup.centralizer {sigma}) / orderOf sigma := by
    rw [hupper]
    exact Nat.eq_div_of_mul_eq_left (orderOf_pos sigma).ne' hcount
  calc
    Nat.card {P : HeightOneSpectrum (𝓞 ↥(fixedField (Subgroup.zpowers sigma))) //
        P.under (𝓞 K) = p ∧
          P ∈ frobeniusPrimeSet ↥(fixedField (Subgroup.zpowers sigma)) L
            (ConjClasses.mk sigma.toFixedFieldAlgEquiv)}
        = Nat.card lowerFiber := rfl
    _ = Nat.card ((fun R : HeightOneSpectrum (𝓞 L) ↦
          R.under (𝓞 ↥(fixedField (Subgroup.zpowers sigma)))) '' upperFiber) := by rw [himage]
    _ = Nat.card upperFiber :=
      Nat.card_congr hinj.bijOn_image.equiv.symm
    _ = Nat.card (Subgroup.centralizer {sigma}) / orderOf sigma := hupper_count
    _ = Nat.card (L ≃ₐ[K] L) / (Nat.card C.carrier * orderOf sigma) := by
      rw [← C.card_div_card_carrier_mul_orderOf_eq_card_centralizer_div_orderOf sigma hsigma]
      exact Subgroup.index_ne_zero_of_finite

end NumberField.Chebotarev
