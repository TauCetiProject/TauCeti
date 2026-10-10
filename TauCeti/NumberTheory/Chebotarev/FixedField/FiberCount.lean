/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.FrobeniusPrimeSet
import TauCeti.NumberTheory.NumberField.Frobenius.FiberCount
import TauCeti.RingTheory.DedekindDomain.PrimesAbove
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

## Main results

* `NumberField.Chebotarev.fixedField_frobenius_fiber_eq_image`: contraction identifies the
  relative fiber with the image of the corresponding absolute Frobenius fiber.
* `NumberField.Chebotarev.inertiaDeg_eq_one_iff_under_mem_frobeniusPrimeSet`: away from the
  ramified primes, a prime of the relative fiber has residue degree one over `K` exactly when the
  prime below it lies in the Frobenius fiber of `sigma`.
* `NumberField.Chebotarev.fixedField_frobenius_fiber_card`: the exact cardinality of the relative
  Frobenius fiber over one prime of `K`.
* `NumberField.Chebotarev.fixedField_frobenius_fiber_inertiaDeg_eq_one_card_mul`: the same count
  for the residue-degree-one primes whose relative Frobenius is any given element of `⟨sigma⟩`.
* `NumberField.Chebotarev.fixedField_frobenius_pow_fiber_card`: the powered fibre count, of the
  residue-degree-one primes whose relative Frobenius has `m`-th power `sigma`.

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

/-- **The forward inclusion.** A prime of the fixed field lying over `p`, whose relative Artin
class is represented by `sigma.toFixedFieldAlgEquiv`, is the contraction of a prime of `L` that
lies over `p` and at which `sigma` is the arithmetic Frobenius. -/
private theorem exists_under_eq_and_isArithFrobAt
    (sigma : L ≃ₐ[K] L) (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ frobeniusPrimeSet K L (ConjClasses.mk sigma))
    {P : HeightOneSpectrum (𝓞 ↥(fixedField (Subgroup.zpowers sigma)))}
    (hPp : P.under (𝓞 K) = p)
    (hP : P ∈ frobeniusPrimeSet ↥(fixedField (Subgroup.zpowers sigma)) L
      (ConjClasses.mk sigma.toFixedFieldAlgEquiv)) :
    ∃ Q : HeightOneSpectrum (𝓞 L),
      (Q.under (𝓞 K) = p ∧ IsArithFrobAt (𝓞 K) sigma Q.asIdeal) ∧
        Q.under (𝓞 ↥(fixedField (Subgroup.zpowers sigma))) = P := by
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

omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- **Unramifiedness passes down to the fixed field.** Suppose every prime of `𝓞 L` over `p` is
unramified over `𝓞 K`, and `Q` lies over `p`. Then a prime of `𝓞 L` over the fixed-field prime
beneath `Q` also lies over `p`, so it is unramified over the fixed field by restriction. -/
private theorem isUnramifiedAt_fixedField_of_under_eq
    (sigma : L ≃ₐ[K] L) (p : HeightOneSpectrum (𝓞 K))
    (hur : ∀ (R : Ideal (𝓞 L)) [R.IsPrime] [R.LiesOver p.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) R)
    (Q : HeightOneSpectrum (𝓞 L)) (hQp : Q.under (𝓞 K) = p)
    (R : Ideal (𝓞 L)) [R.IsPrime]
    [R.LiesOver (Q.under (𝓞 ↥(fixedField (Subgroup.zpowers sigma)))).asIdeal] :
    Algebra.IsUnramifiedAt (𝓞 ↥(fixedField (Subgroup.zpowers sigma))) R := by
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
    exact exists_under_eq_and_isArithFrobAt sigma p hp hPp hP
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
        Algebra.IsUnramifiedAt (𝓞 ↥(fixedField (Subgroup.zpowers sigma))) R :=
      fun R _ _ ↦ isUnramifiedAt_fixedField_of_under_eq sigma p hur Q hQp R
    have : Q.asIdeal.LiesOver
        (Q.under (𝓞 ↥(fixedField (Subgroup.zpowers sigma)))).asIdeal :=
      ⟨HeightOneSpectrum.under_asIdeal _ Q⟩
    refine ⟨?_, mem_frobeniusPrimeSet_mk_of_isArithFrobAt hurE Q.asIdeal (htau_eq ▸ htau)⟩
    exact (HeightOneSpectrum.under_under
      (𝓞 ↥(fixedField (Subgroup.zpowers sigma))) Q).trans hQp

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
  have : Algebra.IsUnramifiedAt (𝓞 K) Q.1 := isUnramifiedAt_of_mem_frobeniusPrimeSet hp' Q.1
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
    _ = Nat.card (Subgroup.centralizer {sigma}) / orderOf sigma :=
      p.frobenius_fiber_card_eq_card_centralizer_div_orderOf Q.1 hQ
    _ = Nat.card (L ≃ₐ[K] L) / (Nat.card C.carrier * orderOf sigma) := by
      rw [← C.card_div_card_carrier_mul_orderOf_eq_card_centralizer_div_orderOf sigma hsigma]
      exact Subgroup.index_ne_zero_of_finite

/-! ### Fibres of an arbitrary element of `⟨σ⟩`, and powered fibres -/

omit [IsGalois K L] in
/-- Every automorphism of `L` over `L ^ ⟨σ⟩` commutes with every other: the group is cyclic,
generated by `σ.toFixedFieldAlgEquiv`. -/
private theorem algEquiv_fixedField_zpowers_mul_comm (σ : L ≃ₐ[K] L)
    (a b : L ≃ₐ[↥(fixedField (Subgroup.zpowers σ))] L) : a * b = b * a :=
  have : IsCyclic (L ≃ₐ[↥(fixedField (Subgroup.zpowers σ))] L) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨_, σ.zpowers_toFixedFieldAlgEquiv_eq_top⟩
  IsCyclic.commGroup.mul_comm a b

omit [IsGalois K L] in
/-- Read over `K`, an automorphism of `L` over `L ^ ⟨σ⟩` is a power of `σ`. -/
private theorem restrictScalars_mem_zpowers (σ : L ≃ₐ[K] L)
    (τ : L ≃ₐ[↥(fixedField (Subgroup.zpowers σ))] L) :
    AlgEquiv.restrictScalars K τ ∈ Subgroup.zpowers σ := by
  refine (IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers σ)).le ?_
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact τ.commutes ⟨x, hx⟩

/-- **The residue-degree-one fibre of one element of `⟨σ⟩`, counted.** Let `p` be a prime of `K`
with Artin class `C`, and let `τ` be an automorphism of `L` over `E = L ^ ⟨σ⟩` that, read over
`K`, lies in `C`. Then the primes `P` of `E` above `p` with residue degree one over `K` and
relative Frobenius `τ` in `L / E` number `#Gal(L/K) / (#C * orderOf σ)`; this is stated
division-free.

The proof counts the primes of `L` above `p` at which `τ` (read over `K`) is the absolute
Frobenius in two ways. Directly, there are `#Centralizer(τ) / orderOf τ` of them. Grouped by the
prime of `E` below them, they are exactly the primes above the residue-degree-one primes of the
relative fibre at which `τ` is the relative Frobenius, and there are `orderOf σ / orderOf τ` of
those above each such prime, `Gal(L/E)` being abelian of order `orderOf σ`.

For `τ = σ.toFixedFieldAlgEquiv` the residue-degree condition is automatic, and this is
`fixedField_frobenius_fiber_card`. -/
theorem fixedField_frobenius_fiber_inertiaDeg_eq_one_card_mul
    (C : ConjClasses (L ≃ₐ[K] L)) (σ : L ≃ₐ[K] L)
    (τ : L ≃ₐ[↥(fixedField (Subgroup.zpowers σ))] L)
    (hτ : AlgEquiv.restrictScalars K τ ∈ C.carrier)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ frobeniusPrimeSet K L C) :
    Nat.card {P : HeightOneSpectrum (𝓞 ↥(fixedField (Subgroup.zpowers σ))) //
      P.under (𝓞 K) = p ∧ P.asIdeal.inertiaDeg (𝓞 K) = 1 ∧
        P ∈ frobeniusPrimeSet ↥(fixedField (Subgroup.zpowers σ)) L (ConjClasses.mk τ)} *
        (Nat.card C.carrier * orderOf σ) = Nat.card (L ≃ₐ[K] L) := by
  set w := AlgEquiv.restrictScalars K τ with hw_def
  have hC : ConjClasses.mk w = C := ConjClasses.mem_carrier_iff_mk_eq.mp hτ
  have hp' : p ∈ frobeniusPrimeSet K L (ConjClasses.mk w) := hC ▸ hp
  have hur : ∀ (R : Ideal (𝓞 L)) [R.IsPrime] [R.LiesOver p.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) R :=
    (mem_frobeniusPrimeSet_iff.mp hp).choose
  have hwσ : w ∈ Subgroup.zpowers σ := restrictScalars_mem_zpowers σ τ
  have hord : orderOf τ = orderOf w :=
    (orderOf_injective (AlgEquiv.restrictScalarsHom K)
      (AlgEquiv.restrictScalarsHom_injective K) τ).symm
  -- The absolute fibre `U` of `w` above `p`.
  let U := {Q : HeightOneSpectrum (𝓞 L) //
    Q.under (𝓞 K) = p ∧ IsArithFrobAt (𝓞 K) w Q.asIdeal}
  obtain ⟨Q0, hQ0⟩ := exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk hp'
  have : Algebra.IsUnramifiedAt (𝓞 K) Q0.1 := hur Q0.1
  have hU : Nat.card U * orderOf w = Nat.card (Subgroup.centralizer {w}) := by
    rw [Nat.card_congr (p.frobeniusFiberEquiv w)]
    exact Ideal.frobenius_fiber_card_mul_orderOf_eq_card_centralizer p.asIdeal Q0.1 hQ0
  -- Facts about a prime of `L` above `p`.
  have hunder (Q : HeightOneSpectrum (𝓞 L)) (hQ : Q.under (𝓞 K) = p) :
      (Q.under (𝓞 ↥(fixedField (Subgroup.zpowers σ)))).under (𝓞 K) = p := by
    rw [HeightOneSpectrum.under_under]
    exact hQ
  have hliesOver (Q : HeightOneSpectrum (𝓞 L)) (hQ : Q.under (𝓞 K) = p) :
      Q.asIdeal.LiesOver p.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal hQ).symm⟩
  have hdeg (Q : HeightOneSpectrum (𝓞 L)) (hQ : Q.under (𝓞 K) = p)
      (hQw : IsArithFrobAt (𝓞 K) w Q.asIdeal) :
      (Q.under (𝓞 ↥(fixedField (Subgroup.zpowers σ)))).asIdeal.inertiaDeg (𝓞 K) = 1 := by
    have := hliesOver Q hQ
    have : Algebra.IsUnramifiedAt (𝓞 K) Q.asIdeal := hur Q.asIdeal
    rw [HeightOneSpectrum.under_asIdeal]
    exact (Ideal.inertiaDeg_under_fixedField_eq_one_iff Q.asIdeal Q.ne_bot _ hQw).2 hwσ
  have hrel (Q : HeightOneSpectrum (𝓞 L)) (hQ : Q.under (𝓞 K) = p)
      (hQw : IsArithFrobAt (𝓞 K) w Q.asIdeal) :
      IsArithFrobAt (𝓞 ↥(fixedField (Subgroup.zpowers σ))) τ Q.asIdeal := by
    have := hliesOver Q hQ
    have : Algebra.IsUnramifiedAt (𝓞 K) Q.asIdeal := hur Q.asIdeal
    obtain ⟨τ', hτ'⟩ := NumberField.exists_isArithFrobAt
      (↥(fixedField (Subgroup.zpowers σ))) Q.asIdeal Q.ne_bot
    have hdQ := hdeg Q hQ hQw
    rw [HeightOneSpectrum.under_asIdeal] at hdQ
    have heq : τ' = τ := AlgEquiv.restrictScalars_injective K
      (NumberField.restrictScalars_eq_of_inertiaDeg_eq_one hQw hτ' hdQ)
    exact heq ▸ hτ'
  have hmemE (Q : HeightOneSpectrum (𝓞 L)) (hQ : Q.under (𝓞 K) = p)
      (hQτ : IsArithFrobAt (𝓞 ↥(fixedField (Subgroup.zpowers σ))) τ Q.asIdeal) :
      Q.under (𝓞 ↥(fixedField (Subgroup.zpowers σ))) ∈
        frobeniusPrimeSet ↥(fixedField (Subgroup.zpowers σ)) L (ConjClasses.mk τ) := by
    have : Q.asIdeal.LiesOver
        (Q.under (𝓞 ↥(fixedField (Subgroup.zpowers σ)))).asIdeal :=
      ⟨HeightOneSpectrum.under_asIdeal _ Q⟩
    exact mem_frobeniusPrimeSet_mk_of_isArithFrobAt
      (fun R _ _ ↦ isUnramifiedAt_fixedField_of_under_eq σ p hur Q hQ R) Q.asIdeal hQτ
  -- The relative fibre `S`, and the contraction `g : U → S`.
  let S := {P : HeightOneSpectrum (𝓞 ↥(fixedField (Subgroup.zpowers σ))) //
    P.under (𝓞 K) = p ∧ P.asIdeal.inertiaDeg (𝓞 K) = 1 ∧
      P ∈ frobeniusPrimeSet ↥(fixedField (Subgroup.zpowers σ)) L (ConjClasses.mk τ)}
  let g : U → S := fun Q ↦ ⟨Q.1.under (𝓞 ↥(fixedField (Subgroup.zpowers σ))),
    hunder Q.1 Q.2.1, hdeg Q.1 Q.2.1 Q.2.2, hmemE Q.1 Q.2.1 (hrel Q.1 Q.2.1 Q.2.2)⟩
  -- Each fibre of `g` is a relative Frobenius fibre of `τ` in `L / E`.
  have hfib (P : S) : Nat.card {Q : U // g Q = P} * orderOf w = orderOf σ := by
    have hPK : P.1.under (𝓞 K) = p := P.2.1
    have hfE : {Q : U // g Q = P} ≃ {R : HeightOneSpectrum (𝓞 L) //
        R.under (𝓞 ↥(fixedField (Subgroup.zpowers σ))) = P.1 ∧
          IsArithFrobAt (𝓞 ↥(fixedField (Subgroup.zpowers σ))) τ R.asIdeal} :=
      { toFun := fun Q ↦ ⟨Q.1.1, congrArg Subtype.val Q.2, hrel Q.1.1 Q.1.2.1 Q.1.2.2⟩
        invFun := fun R ↦
          have hRK : R.1.under (𝓞 K) = p := by
            rw [← HeightOneSpectrum.under_under
              (𝓞 ↥(fixedField (Subgroup.zpowers σ))) R.1, R.2.1, hPK]
          have hRdeg : (R.1.asIdeal.under
              (𝓞 ↥(fixedField (Subgroup.zpowers σ)))).inertiaDeg (𝓞 K) = 1 := by
            rw [← HeightOneSpectrum.under_asIdeal, R.2.1]
            exact P.2.2.1
          ⟨⟨R.1, hRK, NumberField.isArithFrobAt_restrictScalars_of_inertiaDeg_eq_one R.2.2 hRdeg⟩,
            Subtype.ext R.2.1⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    obtain ⟨R0, hR0⟩ := exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk P.2.2.2
    have : Algebra.IsUnramifiedAt (𝓞 ↥(fixedField (Subgroup.zpowers σ))) R0.1 :=
      isUnramifiedAt_of_mem_frobeniusPrimeSet P.2.2.2 R0.1
    have hcent : Subgroup.centralizer {τ} = ⊤ :=
      Subgroup.eq_top_iff' _ |>.mpr fun a ↦
        Subgroup.mem_centralizer_singleton_iff.mpr (algEquiv_fixedField_zpowers_mul_comm σ a τ)
    rw [Nat.card_congr hfE, Nat.card_congr (P.1.frobeniusFiberEquiv τ), ← hord,
      Ideal.frobenius_fiber_card_mul_orderOf_eq_card_centralizer P.1.asIdeal R0.1 hR0, hcent,
      Subgroup.card_top, AlgEquiv.card_algEquiv_fixedField_zpowers]
  -- Finiteness, from the nonvanishing counts.
  have : Finite U := Nat.finite_of_card_ne_zero fun h0 ↦ by
    rw [h0, zero_mul] at hU
    exact Nat.card_pos.ne' hU.symm
  have : Finite S := Finite.of_surjective g fun P ↦ by
    obtain ⟨⟨Q, hQ⟩⟩ := (Nat.card_pos_iff.mp (Nat.pos_of_mul_pos_right
      ((hfib P).symm ▸ orderOf_pos σ))).1
    exact ⟨Q, hQ⟩
  have : Fintype S := Fintype.ofFinite S
  have hsum : Nat.card U * orderOf w = Nat.card S * orderOf σ := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv g), Nat.card_sigma, Finset.sum_mul,
      Finset.sum_congr rfl fun P _ ↦ hfib P, Finset.sum_const, Finset.card_univ,
      Nat.card_eq_fintype_card, smul_eq_mul]
  have hclass : Nat.card C.carrier * Nat.card (Subgroup.centralizer {w}) =
      Nat.card (L ≃ₐ[K] L) := by
    rw [← hC, ConjClasses.card_carrier_mk, Subgroup.index_mul_card]
  rw [← hclass, ← hU, hsum]
  ring

/-- **The powered fibre count of the fixed-field contraction.** Let `p` be a prime of `K` with
Artin class `C`, let `σ ∈ Gal(L/K)` and `E = L ^ ⟨σ⟩`, and let `m` be a natural number. The primes
`P` of `E` above `p` of residue degree one over `K` whose relative Frobenius `Frob_{L/E}(P)`
satisfies `Frob_{L/E}(P) ^ m = σ` number

```text
#{w ∈ C ∩ ⟨σ⟩ | w ^ m = σ} * #Gal(L/K) / (#C * orderOf σ).
```

This is stated division-free; `fixedField_frobenius_pow_fiber_card` is the quotient form.

For `m ≥ 2` the count is supported on the classes `C` containing an `m`-th root of `σ` in `⟨σ⟩`,
which in general are not the class of `σ`: in a cyclic extension of degree five with generator
`g`, a prime with Frobenius `g ^ 3` contributes to the fibre of `g` at `m = 2`, since
`(g ^ 3) ^ 2 = g`. This is why the `ψ`-transfer of the Chebotarev density theorem goes through
`ϑ`, with the prime powers removed on both sides first.

The relative Galois group `Gal(L/E)` is cyclic, so the relative Frobenius of `P` is a single
element, recorded as the `τ` with `P ∈ frobeniusPrimeSet E L [τ]`. -/
theorem fixedField_frobenius_pow_fiber_card_mul
    (C : ConjClasses (L ≃ₐ[K] L)) (σ : L ≃ₐ[K] L) (m : ℕ)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ frobeniusPrimeSet K L C) :
    Nat.card {P : HeightOneSpectrum (𝓞 ↥(fixedField (Subgroup.zpowers σ))) //
      P.under (𝓞 K) = p ∧ P.asIdeal.inertiaDeg (𝓞 K) = 1 ∧
        ∃ τ : L ≃ₐ[↥(fixedField (Subgroup.zpowers σ))] L, τ ^ m = σ.toFixedFieldAlgEquiv ∧
          P ∈ frobeniusPrimeSet ↥(fixedField (Subgroup.zpowers σ)) L (ConjClasses.mk τ)} *
        (Nat.card C.carrier * orderOf σ) =
      Nat.card {w : L ≃ₐ[K] L // w ∈ C.carrier ∧ w ∈ Subgroup.zpowers σ ∧ w ^ m = σ} *
        Nat.card (L ≃ₐ[K] L) := by
  -- The tags `T`: the `m`-th roots of `σ.toFixedFieldAlgEquiv` lying in `C` when read over `K`.
  let T := {τ : L ≃ₐ[↥(fixedField (Subgroup.zpowers σ))] L //
    τ ^ m = σ.toFixedFieldAlgEquiv ∧ AlgEquiv.restrictScalars K τ ∈ C.carrier}
  let S := fun τ : T ↦ {P : HeightOneSpectrum (𝓞 ↥(fixedField (Subgroup.zpowers σ))) //
    P.under (𝓞 K) = p ∧ P.asIdeal.inertiaDeg (𝓞 K) = 1 ∧
      P ∈ frobeniusPrimeSet ↥(fixedField (Subgroup.zpowers σ)) L (ConjClasses.mk τ.1)}
  have hS (τ : T) : Nat.card (S τ) * (Nat.card C.carrier * orderOf σ) =
      Nat.card (L ≃ₐ[K] L) :=
    fixedField_frobenius_fiber_inertiaDeg_eq_one_card_mul C σ τ.1 τ.2.2 p hp
  have : ∀ τ, Finite (S τ) := fun τ ↦ Nat.finite_of_card_ne_zero fun h0 ↦ by
    have := hS τ
    rw [h0, zero_mul] at this
    exact Nat.card_pos.ne' this.symm
  -- The fibre over the tags is the disjoint union of the fibres of the tags.
  have hsplit : (Σ τ : T, S τ) ≃
      {P : HeightOneSpectrum (𝓞 ↥(fixedField (Subgroup.zpowers σ))) //
        P.under (𝓞 K) = p ∧ P.asIdeal.inertiaDeg (𝓞 K) = 1 ∧
          ∃ τ : L ≃ₐ[↥(fixedField (Subgroup.zpowers σ))] L, τ ^ m = σ.toFixedFieldAlgEquiv ∧
            P ∈ frobeniusPrimeSet ↥(fixedField (Subgroup.zpowers σ)) L (ConjClasses.mk τ)} := by
    refine Equiv.ofBijective (fun x ↦ ⟨x.2.1, x.2.2.1, x.2.2.2.1, x.1.1, x.1.2.1, x.2.2.2.2⟩)
      ⟨?_, ?_⟩
    · rintro ⟨⟨τ₁, h₁⟩, P₁⟩ ⟨⟨τ₂, h₂⟩, P₂⟩ h
      have hP : P₁.1 = P₂.1 := congrArg Subtype.val h
      obtain rfl : τ₁ = τ₂ := by
        by_contra hne
        have hne' : ConjClasses.mk τ₁ ≠ ConjClasses.mk τ₂ := by
          rw [Ne, ConjClasses.mk_eq_mk_iff_isConj]
          rintro ⟨c, hc⟩
          apply hne
          rw [SemiconjBy, algEquiv_fixedField_zpowers_mul_comm σ τ₂ (↑c)] at hc
          exact mul_left_cancel hc
        exact Set.disjoint_left.mp (disjoint_frobeniusPrimeSet hne') P₁.2.2.2 (hP ▸ P₂.2.2.2)
      obtain rfl : P₁ = P₂ := Subtype.ext hP
      rfl
    · rintro ⟨P, hPp, hPdeg, τ, hτm, hPτ⟩
      -- The absolute Frobenius below a residue-degree-one prime is `τ` read over `K`.
      obtain ⟨R, hR⟩ := exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk hPτ
      have hRE : R.1.under (𝓞 ↥(fixedField (Subgroup.zpowers σ))) = P.asIdeal := R.2.2.over.symm
      have hRK : R.1.under (𝓞 K) = p.asIdeal := by
        rw [← Ideal.under_under (B := 𝓞 ↥(fixedField (Subgroup.zpowers σ))) R.1, hRE,
          ← HeightOneSpectrum.under_asIdeal, hPp]
      have : R.1.LiesOver p.asIdeal := ⟨hRK.symm⟩
      have habs := NumberField.isArithFrobAt_restrictScalars_of_inertiaDeg_eq_one hR
        (hRE ▸ hPdeg)
      have hmk : ConjClasses.mk (AlgEquiv.restrictScalars K τ) = C := by
        obtain ⟨hur, hart⟩ := mem_frobeniusPrimeSet_iff.mp hp
        rw [← hart]
        exact (artinSymbol_eq_mk_of_isArithFrobAt p.asIdeal hur R.1 _ habs).symm
      exact ⟨⟨⟨τ, hτm, ConjClasses.mem_carrier_iff_mk_eq.mpr hmk⟩, ⟨P, hPp, hPdeg, hPτ⟩⟩, rfl⟩
  -- The tags correspond to the `m`-th roots of `σ` in `C ∩ ⟨σ⟩`.
  have htags : T ≃ {w : L ≃ₐ[K] L // w ∈ C.carrier ∧ w ∈ Subgroup.zpowers σ ∧ w ^ m = σ} := by
    refine Equiv.ofBijective (fun τ ↦ ⟨AlgEquiv.restrictScalars K τ.1, τ.2.2,
      restrictScalars_mem_zpowers σ τ.1, ?_⟩) ⟨?_, ?_⟩
    · rw [← AlgEquiv.restrictScalarsHom_apply, ← map_pow, τ.2.1,
        AlgEquiv.restrictScalarsHom_apply, AlgEquiv.restrictScalars_toFixedFieldAlgEquiv]
    · intro τ₁ τ₂ h
      exact Subtype.ext (AlgEquiv.restrictScalars_injective K (congrArg Subtype.val h))
    · rintro ⟨w, hwC, ⟨k, rfl⟩, hwm⟩
      have hk : AlgEquiv.restrictScalars K (σ.toFixedFieldAlgEquiv ^ k) = σ ^ k := by
        rw [← AlgEquiv.restrictScalarsHom_apply, map_zpow, AlgEquiv.restrictScalarsHom_apply,
          AlgEquiv.restrictScalars_toFixedFieldAlgEquiv]
      refine ⟨⟨σ.toFixedFieldAlgEquiv ^ k, ?_, hk ▸ hwC⟩, Subtype.ext hk⟩
      apply AlgEquiv.restrictScalars_injective K
      rw [← AlgEquiv.restrictScalarsHom_apply, map_pow, AlgEquiv.restrictScalarsHom_apply, hk,
        AlgEquiv.restrictScalars_toFixedFieldAlgEquiv]
      exact hwm
  have : Fintype T := Fintype.ofFinite T
  rw [← Nat.card_congr hsplit, Nat.card_sigma, Finset.sum_mul,
    Finset.sum_congr rfl fun τ _ ↦ hS τ, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, Nat.card_congr htags, smul_eq_mul]

/-- **The powered fibre count, as a quotient.** The number of primes of `L ^ ⟨σ⟩` above `p`, of
residue degree one over `K`, whose relative Frobenius has `m`-th power `σ`, is
`#{w ∈ C ∩ ⟨σ⟩ | w ^ m = σ} * #Gal(L/K) / (#C * orderOf σ)` for the Artin class `C` of `p`. The
division is exact by `fixedField_frobenius_pow_fiber_card_mul`. -/
theorem fixedField_frobenius_pow_fiber_card
    (C : ConjClasses (L ≃ₐ[K] L)) (σ : L ≃ₐ[K] L) (m : ℕ)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ frobeniusPrimeSet K L C) :
    Nat.card {P : HeightOneSpectrum (𝓞 ↥(fixedField (Subgroup.zpowers σ))) //
      P.under (𝓞 K) = p ∧ P.asIdeal.inertiaDeg (𝓞 K) = 1 ∧
        ∃ τ : L ≃ₐ[↥(fixedField (Subgroup.zpowers σ))] L, τ ^ m = σ.toFixedFieldAlgEquiv ∧
          P ∈ frobeniusPrimeSet ↥(fixedField (Subgroup.zpowers σ)) L (ConjClasses.mk τ)} =
      Nat.card {w : L ≃ₐ[K] L // w ∈ C.carrier ∧ w ∈ Subgroup.zpowers σ ∧ w ^ m = σ} *
        Nat.card (L ≃ₐ[K] L) / (Nat.card C.carrier * orderOf σ) := by
  obtain ⟨g, hg⟩ := ConjClasses.exists_rep C
  have : Nonempty C.carrier := ⟨⟨g, ConjClasses.mem_carrier_iff_mk_eq.mpr hg⟩⟩
  exact Nat.eq_div_of_mul_eq_left (Nat.mul_pos Nat.card_pos (orderOf_pos σ)).ne'
    (fixedField_frobenius_pow_fiber_card_mul C σ m p hp)

end NumberField.Chebotarev
