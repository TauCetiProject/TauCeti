/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Mathlib.RingTheory.Valuation.ValuationRing
public import TauCeti.RingTheory.Localization.AsSubring
public import TauCeti.RingTheory.Valuation.Center
import TauCeti.RingTheory.Frobenius
import TauCeti.RingTheory.Valuation.RamificationGroup

/-!
# Valuation subrings centred at a prime, and the localization at the centre

Let `B` be a ring with fraction field `L`. A valuation subring `A` of `L` containing (the image of)
`B` has a *centre* on `B`: the prime ideal of the `b ∈ B` that are nonunits of `A`, Tau Ceti's
`Valuation.centerIdeal`. Write `A.IsCenteredAt P` when `A` contains `B` with centre `P`.

When the localization `B_P` is a valuation ring, the only valuation subring of `L` centred at `P`
is `B_P` itself, realized inside `L`: an element `x ∈ A` either lies in `B_P` or has inverse
`a / s` with `s ∉ P`, and then `a ∉ P` as well since `a / s` is a unit of `A`. So when every
localization of `B` at a prime is a valuation ring (that is, `B` is a Prüfer domain), the valuation
subrings of `L` containing `B` correspond to the primes of `B` through their centres
(`ValuationSubring.equivPrimeSpectrum`). Under this correspondence, for a group `G` acting on `B`
and `L` compatibly, the centre of `g • A` is `g • P`, so the stabilizer of `A` is the stabilizer
of `P`, and the elements of `G` acting on `A` by `x ↦ x ^ q` modulo the nonunits of `A` are those
acting on `B` by `b ↦ b ^ q` modulo `P`. For `q = 1` this identifies the two inertia subgroups.
For `G = Gal(L/K)` these are statements about Mathlib's `ValuationSubring.decompositionSubgroup`,
`ValuationSubring.inertiaSubgroup`, `Ideal.inertia` and `IsArithFrobAt`.

The typical `B` is the integral closure of a Dedekind domain in an algebraic, possibly infinite,
separable extension of its fraction field, for instance the ring of all algebraic integers in an
algebraic closure of `ℚ`: its localizations at primes are valuation rings
(`IsIntegralClosure.preValuationRing_atPrime` in `TauCeti/RingTheory/DedekindDomain/Prufer.lean`).
For Dedekind `B` itself, at a nonzero prime, the localization is Mathlib's
`IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime`
(`IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_asIdeal`, in the same file).

The predicate `ValuationSubring.IsCenteredAt A P` (`A` contains `B` and `P` is its centre on `B`)
and its equivariance `ValuationSubring.IsCenteredAt.smul` are in
`TauCeti/RingTheory/Valuation/Center.lean`.

## Main definitions

* `Ideal.valuationSubringAtPrime L P`: for `B_P` a valuation ring, `B_P` as a valuation subring
  of `L`.
* `ValuationSubring.equivPrimeSpectrum`: for `B` all of whose localizations at primes are
  valuation rings, the valuation subrings of `L` containing `B` correspond to the primes of `B`.

## Main results

* `ValuationSubring.IsCenteredAt.eq_valuationSubringAtPrime`: a valuation subring centred at `P`
  is `B_P`.
* `Ideal.valuationSubringAtPrime_le_valuationSubringAtPrime_iff`: `B_Q ≤ B_P` exactly when
  `P ≤ Q`.
* `Ideal.smul_valuationSubringAtPrime` and `ValuationSubring.coe_equivPrimeSpectrum_symm_smul`:
  `g • B_P = B_{g • P}`, so the correspondence with primes is equivariant.
* `ValuationSubring.IsCenteredAt.stabilizer_eq`: the stabilizers of `A` and of `P` agree.
* `ValuationSubring.IsCenteredAt.forall_smul_sub_pow_mem_iff`: `g` raises elements to the `q`-th
  power modulo `P` exactly when it does so modulo the nonunits of `A`.
* `ValuationSubring.IsCenteredAt.decompositionSubgroup_eq`,
  `ValuationSubring.IsCenteredAt.map_inertiaSubgroup_eq` and
  `ValuationSubring.IsCenteredAt.isArithFrobAt_iff`: for `Gal(L/K)`, the decomposition group,
  inertia group and arithmetic Frobenius elements at `A` are those at its centre.

## References

* [N. Bourbaki, *Commutative Algebra*], Chapter VI, §1, no. 2 and §8, for valuation rings
  dominating a local ring and the localizations of a Prüfer domain.
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9, for decomposition and
  inertia groups and Frobenius elements at a prime.

## Provenance

The direction from a valuation subring to its centre of the Frobenius and inertia comparisons
(`ValuationSubring.IsCenteredAt.isArithFrobAt_iff` and
`ValuationSubring.IsCenteredAt.map_inertiaSubgroup_eq`) was first proved in the
`riemann-hypothesis` formalisation (https://github.com/leanprover-community/riemann-hypothesis,
branch `tc-galois-5-frobenius`, commit `c62bdab14fd`,
`src/Lib/ClassField/Places/FrobeniusComparison.lean`, declarations `New.IsFrob.isArithFrobAt` and
`New.inertiaGroup_le_inertia`). **Adapted, not copied**: those prove only that direction, for
that project's `New.IsFrob` and the algebraic closure of a number field; here both directions are
proved for any ring `B` whose localization at the centre is a valuation ring, the converse
through the identification of a valuation subring with the localization at its centre, and they
are stated with Mathlib's decomposition, inertia and Frobenius predicates.
-/

public section

open scoped Pointwise nonZeroDivisors

variable {B L : Type*} [CommRing B] [Field L] [Algebra B L]

namespace Ideal

variable (L) [IsFractionRing B L] (P : Ideal B) [P.IsPrime]

/-- **The localization at a prime is a valuation ring exactly when it is one inside `L`**: every
element of `L`, or its inverse, is a fraction `a / s` with `s ∉ P`. -/
theorem preValuationRing_atPrime_iff :
    PreValuationRing (Localization.AtPrime P) ↔
      ∀ x : L, x ∈ Localization.subalgebra.ofField L P.primeCompl
          (P.primeCompl_le_nonZeroDivisors_of_isFractionRing L) ∨
        x⁻¹ ∈ Localization.subalgebra.ofField L P.primeCompl
          (P.primeCompl_le_nonZeroDivisors_of_isFractionRing L) := by
  set S := Localization.subalgebra.ofField L P.primeCompl
    (P.primeCompl_le_nonZeroDivisors_of_isFractionRing L)
  let e := IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P) S
  have hint (x : L) : IsLocalization.IsInteger S x ↔ x ∈ S :=
    ⟨fun ⟨s, hs⟩ ↦ hs ▸ s.property, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  simp_rw [← hint]
  refine ⟨fun _ ↦ ?_, fun h ↦ ?_⟩
  · have : PreValuationRing S :=
      Function.Surjective.preValuationRing (e : Localization.AtPrime P →ₙ* S) e.surjective
    have : ValuationRing S := .mk
    exact ValuationRing.isInteger_or_isInteger S
  · have : ValuationRing S := (ValuationRing.iff_isInteger_or_isInteger S L).mpr h
    exact Function.Surjective.preValuationRing (e.symm : S →ₙ* Localization.AtPrime P)
      e.symm.surjective

variable [PreValuationRing (Localization.AtPrime P)]

/-- **The localization at a prime as a valuation subring.** When the localization `B_P` is a
valuation ring, it is realized inside the fraction field `L` as a valuation subring, whose
elements are the fractions `a / s` with `s ∉ P` (`Ideal.mem_valuationSubringAtPrime_iff`). It is a
`B`-algebra and a localization of `B` at `P.primeCompl` (`IsLocalization`), with the algebra
structure of `Localization.subalgebra.ofField`. -/
noncomputable def valuationSubringAtPrime : ValuationSubring L :=
  .ofSubring (Localization.subalgebra.ofField L P.primeCompl
    (P.primeCompl_le_nonZeroDivisors_of_isFractionRing L)).toSubring
    ((P.preValuationRing_atPrime_iff L).mp inferInstance)

/-- The underlying subring of `B_P`, realized inside `L`, is Mathlib's
`Localization.subalgebra.ofField`. -/
theorem valuationSubringAtPrime_toSubring :
    (P.valuationSubringAtPrime L).toSubring = (Localization.subalgebra.ofField L P.primeCompl
      (P.primeCompl_le_nonZeroDivisors_of_isFractionRing L)).toSubring :=
  (rfl)

variable {L P}

/-- The elements of `B_P`, realized inside `L`, are the fractions `a / s` with `s ∉ P`. -/
theorem mem_valuationSubringAtPrime_iff {x : L} :
    x ∈ P.valuationSubringAtPrime L ↔
      ∃ a, ∃ s ∉ P, x = algebraMap B L a * (algebraMap B L s)⁻¹ := by
  rw [← ValuationSubring.mem_toSubring, valuationSubringAtPrime_toSubring,
    Subalgebra.mem_toSubring, Localization.subalgebra.mem_ofField_iff]
  simp only [Ideal.mem_primeCompl_iff]

/-- `B_P`, realized inside `L`, is a `B`-algebra through the algebra map `B → L`, which lands in
`B_P`. -/
noncomputable instance : Algebra B (P.valuationSubringAtPrime L) :=
  ((algebraMap B L).codRestrict (P.valuationSubringAtPrime L) fun b ↦
    mem_valuationSubringAtPrime_iff.mpr ⟨b, 1, P.primeCompl.one_mem, by
      rw [map_one, inv_one, mul_one]⟩).toAlgebra

/-- The algebra map `B → B_P`, followed by the inclusion of `B_P` into `L`, is the algebra map
`B → L`. -/
@[simp]
theorem coe_algebraMap_valuationSubringAtPrime (b : B) :
    (algebraMap B (P.valuationSubringAtPrime L) b : L) = algebraMap B L b :=
  (rfl)

/-- The algebra map `B → L` factors through `B_P`. -/
instance : IsScalarTower B (P.valuationSubringAtPrime L) L :=
  .of_algebraMap_eq fun b ↦ (coe_algebraMap_valuationSubringAtPrime (P := P) b).symm

/-- `B_P`, realized inside `L`, is a localization of `B` at the complement of `P`: this is
Mathlib's `Localization.subalgebra.isLocalization_ofField`. -/
instance : IsLocalization P.primeCompl (P.valuationSubringAtPrime L) :=
  have := Localization.subalgebra.isLocalization_ofField L P.primeCompl
    (P.primeCompl_le_nonZeroDivisors_of_isFractionRing L)
  have hmem (x : L) : x ∈ Localization.subalgebra.ofField L P.primeCompl
      (P.primeCompl_le_nonZeroDivisors_of_isFractionRing L) ↔ x ∈ P.valuationSubringAtPrime L := by
    rw [← ValuationSubring.mem_toSubring, valuationSubringAtPrime_toSubring]
    rfl
  IsLocalization.isLocalization_of_algEquiv P.primeCompl <| AlgEquiv.ofRingEquiv
    (f := { Equiv.subtypeEquivRight hmem with
      map_mul' := fun _ _ ↦ rfl, map_add' := fun _ _ ↦ rfl }) fun _ ↦ rfl

/-- `B_P` is centred at `P`. -/
theorem isCenteredAt_valuationSubringAtPrime : (P.valuationSubringAtPrime L).IsCenteredAt P where
  algebraMap_mem b := mem_valuationSubringAtPrime_iff.mpr
    ⟨b, 1, P.primeCompl.one_mem, by rw [map_one, inv_one, mul_one]⟩
  algebraMap_mem_nonunits_iff b := by
    rw [← coe_algebraMap_valuationSubringAtPrime (P := P), ValuationSubring.coe_mem_nonunits_iff]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff _ P b

/-- **Localizations at primes reverse inclusion**: `B_Q ≤ B_P`, realized inside `L`, exactly when
`P ≤ Q`. So the correspondence between valuation subrings and primes is order-reversing. -/
theorem valuationSubringAtPrime_le_valuationSubringAtPrime_iff {Q : Ideal B} [Q.IsPrime]
    [PreValuationRing (Localization.AtPrime Q)] :
    Q.valuationSubringAtPrime L ≤ P.valuationSubringAtPrime L ↔ P ≤ Q := by
  refine ⟨fun hle b hb ↦ ?_, fun hPQ x hx ↦ ?_⟩
  · -- If `b ∉ Q` then `1 / b ∈ B_Q ≤ B_P`, so `b ∈ P` would be a unit of `B_P`.
    by_contra hbQ
    have hb0 : algebraMap B L b ≠ 0 := Ideal.algebraMap_ne_zero_of_notMem hbQ
    have hinv : (P.valuationSubringAtPrime L).valuation (algebraMap B L b)⁻¹ ≤ 1 :=
      (ValuationSubring.valuation_le_one_iff _ _).mpr <| hle <| mem_valuationSubringAtPrime_iff.mpr
        ⟨1, b, hbQ, by rw [map_one, one_mul]⟩
    have hcen := isCenteredAt_valuationSubringAtPrime (L := L) (P := P)
    have hlt := (hcen.valuation_algebraMap_lt_one_iff b).mpr hb
    refine (lt_irrefl (1 : ValuationSubring.ValueGroup (P.valuationSubringAtPrime L)) ?_)
    calc (1 : ValuationSubring.ValueGroup (P.valuationSubringAtPrime L))
        = (P.valuationSubringAtPrime L).valuation (algebraMap B L b * (algebraMap B L b)⁻¹) := by
          rw [mul_inv_cancel₀ hb0, map_one]
      _ ≤ (P.valuationSubringAtPrime L).valuation (algebraMap B L b) := by
          rw [map_mul]
          exact mul_le_of_le_one_right' hinv
      _ < 1 := hlt
  · obtain ⟨a, s, hs, rfl⟩ := mem_valuationSubringAtPrime_iff.mp hx
    exact mem_valuationSubringAtPrime_iff.mpr ⟨a, s, fun hsP ↦ hs (hPQ hsP), rfl⟩

end Ideal

namespace ValuationSubring

namespace IsCenteredAt

variable [IsFractionRing B L] {A : ValuationSubring L} {P : Ideal B}

/-- An element of a valuation subring centred at `P` is a fraction `a / s` with `s ∉ P`, provided
`B_P` is a valuation ring. -/
theorem exists_eq_mul_inv (h : A.IsCenteredAt P) [P.IsPrime]
    [PreValuationRing (Localization.AtPrime P)] {x : L} (hx : x ∈ A) :
    ∃ a, ∃ s ∉ P, x = algebraMap B L a * (algebraMap B L s)⁻¹ := by
  rcases (P.valuationSubringAtPrime L).mem_or_inv_mem x with hx' | hx'
  · exact Ideal.mem_valuationSubringAtPrime_iff.mp hx'
  obtain ⟨a, s, hs, hxa⟩ := Ideal.mem_valuationSubringAtPrime_iff.mp hx'
  by_cases hx0 : x = 0
  · exact ⟨0, 1, P.primeCompl.one_mem, by rw [hx0, map_zero, zero_mul]⟩
  refine ⟨s, a, fun ha ↦ hs ?_, ?_⟩
  · -- `s = x * a` is a nonunit of `A`, as `x ∈ A` and `a` is a nonunit of `A`
    rw [← h.valuation_algebraMap_lt_one_iff] at ha ⊢
    have hs0 : algebraMap B L s ≠ 0 := Ideal.algebraMap_ne_zero_of_notMem hs
    have hsx : algebraMap B L s = x * algebraMap B L a := by
      field_simp at hxa
      linear_combination hxa
    rw [hsx, map_mul]
    exact (mul_le_of_le_one_left' ((A.valuation_le_one_iff x).mpr hx)).trans_lt ha
  · rw [← inv_inv x, hxa, mul_inv, inv_inv, mul_comm]

/-- **A valuation subring centred at `P` is the localization `B_P`**, when `B_P` is a valuation
ring. -/
theorem eq_valuationSubringAtPrime (h : A.IsCenteredAt P) [P.IsPrime]
    [PreValuationRing (Localization.AtPrime P)] : A = P.valuationSubringAtPrime L := by
  ext x
  rw [Ideal.mem_valuationSubringAtPrime_iff]
  refine ⟨h.exists_eq_mul_inv, ?_⟩
  rintro ⟨a, s, hs, rfl⟩
  rw [← valuation_le_one_iff, map_mul, map_inv₀, (h.valuation_algebraMap_eq_one_iff s).mpr hs,
    inv_one, mul_one]
  exact h.valuation_algebraMap_le_one a

/-- **Two valuation subrings with the same centre `P` are equal**, when `B_P` is a valuation
ring. -/
theorem eq (h : A.IsCenteredAt P) {A' : ValuationSubring L} (h' : A'.IsCenteredAt P) [P.IsPrime]
    [PreValuationRing (Localization.AtPrime P)] : A = A' :=
  h.eq_valuationSubringAtPrime.trans h'.eq_valuationSubringAtPrime.symm

end IsCenteredAt

/-- **Valuation subrings containing `B` are its primes.** When every localization of `B` at a
prime is a valuation ring (`B` is a Prüfer domain with fraction field `L`), sending a valuation
subring of `L` containing `B` to its centre is a bijection onto the prime spectrum of `B`, with
inverse `P ↦ B_P`. -/
noncomputable def equivPrimeSpectrum [IsFractionRing B L]
    (hB : ∀ (P : Ideal B) [P.IsPrime], PreValuationRing (Localization.AtPrime P)) :
    {A : ValuationSubring L // ∀ b : B, algebraMap B L b ∈ A} ≃ PrimeSpectrum B where
  toFun A :=
    have hA (b : B) := (A.val.valuation_le_one_iff _).mpr (A.property b)
    ⟨A.val.valuation.centerIdeal B hA, Valuation.isPrime_centerIdeal hA⟩
  invFun P :=
    have := hB P.asIdeal
    ⟨P.asIdeal.valuationSubringAtPrime L, Ideal.isCenteredAt_valuationSubringAtPrime.algebraMap_mem⟩
  left_inv A := by
    have hA (b : B) := (A.val.valuation_le_one_iff _).mpr (A.property b)
    have := Valuation.isPrime_centerIdeal hA
    have := hB (A.val.valuation.centerIdeal B hA)
    exact Subtype.ext (A.val.isCenteredAt_centerIdeal hA).eq_valuationSubringAtPrime.symm
  right_inv P := by
    have := hB P.asIdeal
    exact PrimeSpectrum.ext
      (Ideal.isCenteredAt_valuationSubringAtPrime.eq_centerIdeal (B := B) (L := L)).symm

/-- The prime corresponding to a valuation subring containing `B` is its centre on `B`. -/
@[simp]
theorem asIdeal_equivPrimeSpectrum_apply [IsFractionRing B L]
    (hB : ∀ (P : Ideal B) [P.IsPrime], PreValuationRing (Localization.AtPrime P))
    (A : {A : ValuationSubring L // ∀ b : B, algebraMap B L b ∈ A}) :
    ((equivPrimeSpectrum hB A).asIdeal : Ideal B) =
      A.val.valuation.centerIdeal B fun b ↦ (A.val.valuation_le_one_iff _).mpr (A.property b) :=
  (rfl)

/-- The valuation subring corresponding to a prime `P` is the localization `B_P`. -/
@[simp]
theorem coe_equivPrimeSpectrum_symm_apply [IsFractionRing B L]
    (hB : ∀ (P : Ideal B) [P.IsPrime], PreValuationRing (Localization.AtPrime P))
    (P : PrimeSpectrum B) :
    ((equivPrimeSpectrum (L := L) hB).symm P : ValuationSubring L) =
      @Ideal.valuationSubringAtPrime B L _ _ _ _ P.asIdeal _ (hB P.asIdeal) :=
  (rfl)

/-! ### Group actions -/

namespace IsCenteredAt

variable {G : Type*} [Group G] [MulSemiringAction G B] [MulSemiringAction G L]
  [SMulDistribClass G B L] [IsFractionRing B L] {A : ValuationSubring L} {P : Ideal B}

/-- **The stabilizer of a valuation subring is the stabilizer of its centre** `P`, when `B_P` is a
valuation ring. -/
theorem stabilizer_eq (h : A.IsCenteredAt P) [P.IsPrime]
    [PreValuationRing (Localization.AtPrime P)] :
    MulAction.stabilizer G A = MulAction.stabilizer G P := by
  refine le_antisymm h.stabilizer_le fun g hg ↦ MulAction.mem_stabilizer_iff.mpr ?_
  have h' := h.smul g
  rw [MulAction.mem_stabilizer_iff.mp hg] at h'
  exact h'.eq h

/-- **Frobenius elements at a valuation subring and at its centre.** When `B_P` is a valuation
ring, `g` raises every element of `B` to the `q`-th power modulo `P` exactly when it raises every
element of `A` to the `q`-th power modulo the nonunits of `A`. For `q = 1` these are the two
inertia conditions. -/
theorem forall_smul_sub_pow_mem_iff (h : A.IsCenteredAt P) [P.IsPrime]
    [PreValuationRing (Localization.AtPrime P)] {g : G} {q : ℕ} :
    (∀ b : B, g • b - b ^ q ∈ P) ↔ ∀ x ∈ A, g • x - x ^ q ∈ A.nonunits := by
  refine ⟨fun hg x hx ↦ ?_, h.smul_sub_pow_mem_of_forall⟩
  have hgP := MulAction.mem_stabilizer_iff.mp (Ideal.mem_stabilizer_of_forall_smul_sub_pow_mem hg)
  obtain ⟨a, s, hs, rfl⟩ := h.exists_eq_mul_inv hx
  have hgs : g • s ∉ P := by
    rwa [← hgP, Ideal.smul_mem_pointwise_smul_iff]
  have hden : g • s * s ^ q ∉ P := P.primeCompl.mul_mem hgs (P.primeCompl.pow_mem hs q)
  -- `g • (a / s) - (a / s) ^ q = (g a * s ^ q - a ^ q * g s) / (g s * s ^ q)`
  have key : g • (algebraMap B L a * (algebraMap B L s)⁻¹) - (algebraMap B L a *
      (algebraMap B L s)⁻¹) ^ q = algebraMap B L (g • a * s ^ q - a ^ q * g • s) *
        (algebraMap B L (g • s * s ^ q))⁻¹ := by
    have : algebraMap B L s ≠ 0 := Ideal.algebraMap_ne_zero_of_notMem hs
    have : algebraMap B L (g • s) ≠ 0 := Ideal.algebraMap_ne_zero_of_notMem hgs
    rw [smul_mul', smul_inv'', ← algebraMap.smul', ← algebraMap.smul']
    simp only [map_mul, map_sub, map_pow, mul_pow, inv_pow]
    field_simp
  rw [mem_nonunits_iff, key, map_mul, map_inv₀, (h.valuation_algebraMap_eq_one_iff _).mpr hden,
    inv_one, mul_one, h.valuation_algebraMap_lt_one_iff,
    show g • a * s ^ q - a ^ q * g • s = (g • a - a ^ q) * s ^ q - a ^ q * (g • s - s ^ q) by ring]
  exact P.sub_mem (P.mul_mem_right _ (hg a)) (P.mul_mem_left _ (hg s))

end IsCenteredAt

section Action

variable {G : Type*} [Group G] [MulSemiringAction G B] [MulSemiringAction G L]
  [SMulDistribClass G B L] [IsFractionRing B L]

/-- **Equivariance of the localization at a prime**: the image under `g` of `B_P`, realized inside
`L`, is `B_{g • P}`, when both localizations are valuation rings. -/
@[simp]
theorem _root_.Ideal.smul_valuationSubringAtPrime (g : G) (P : Ideal B) [P.IsPrime]
    [PreValuationRing (Localization.AtPrime P)] [PreValuationRing (Localization.AtPrime (g • P))] :
    g • P.valuationSubringAtPrime L = (g • P).valuationSubringAtPrime L :=
  (Ideal.isCenteredAt_valuationSubringAtPrime.smul g).eq Ideal.isCenteredAt_valuationSubringAtPrime

/-- **Equivariance of `ValuationSubring.equivPrimeSpectrum`**: the valuation subring corresponding
to `g • P` is the image under `g` of the one corresponding to `P`. -/
theorem coe_equivPrimeSpectrum_symm_smul
    (hB : ∀ (P : Ideal B) [P.IsPrime], PreValuationRing (Localization.AtPrime P)) (g : G)
    (P : PrimeSpectrum B) :
    ((equivPrimeSpectrum (L := L) hB).symm (g • P) : ValuationSubring L) =
      g • ((equivPrimeSpectrum (L := L) hB).symm P : ValuationSubring L) := by
  have := hB P.asIdeal
  have := hB (g • P.asIdeal)
  rw [coe_equivPrimeSpectrum_symm_apply, coe_equivPrimeSpectrum_symm_apply]
  -- `(g • P).asIdeal` is `g • P.asIdeal` by definition (`PrimeSpectrum.asIdeal_smul` is `rfl`);
  -- `rw` cannot use it, as the prime instance in `valuationSubringAtPrime` depends on the ideal
  exact (Ideal.smul_valuationSubringAtPrime g P.asIdeal).symm

end Action

/-! ### Galois groups -/

namespace IsCenteredAt

variable {K : Type*} [Field K] [Algebra K L] [MulSemiringAction (L ≃ₐ[K] L) B]
  [SMulDistribClass (L ≃ₐ[K] L) B L] [IsFractionRing B L] {A : ValuationSubring L} {P : Ideal B}
  [P.IsPrime] [PreValuationRing (Localization.AtPrime P)]

/-- **The decomposition group of a valuation subring is that of its centre**: Mathlib's
`ValuationSubring.decompositionSubgroup` of `A` is the stabilizer in `Gal(L/K)` of the centre
`P`, when `B_P` is a valuation ring. -/
theorem decompositionSubgroup_eq (h : A.IsCenteredAt P) :
    A.decompositionSubgroup K = MulAction.stabilizer (L ≃ₐ[K] L) P :=
  h.stabilizer_eq

/-- **The inertia group of a valuation subring is that of its centre**: the image in `Gal(L/K)`
of Mathlib's `ValuationSubring.inertiaSubgroup` of `A` is Mathlib's inertia subgroup
`Ideal.inertia` of the centre `P`, when `B_P` is a valuation ring. -/
theorem map_inertiaSubgroup_eq (h : A.IsCenteredAt P) :
    (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype =
      P.inertia (L ≃ₐ[K] L) := by
  ext σ
  rw [mem_map_inertiaSubgroup_iff, Ideal.mem_inertia]
  simpa only [pow_one, AlgEquiv.smul_def] using
    (h.forall_smul_sub_pow_mem_iff (g := σ) (q := 1)).symm

/-- **Arithmetic Frobenius elements at a valuation subring and at its centre**: `σ ∈ Gal(L/K)` is
an arithmetic Frobenius element at the centre `P` in Mathlib's sense (`IsArithFrobAt`, for a base
ring `R` of `B` with `q = #(R ⧸ P ∩ R)`) exactly when it lies in the decomposition group of `A`
and acts on the residue field of `A` as `y ↦ y ^ q`, when `B_P` is a valuation ring. -/
theorem isArithFrobAt_iff (h : A.IsCenteredAt P) {R : Type*} [CommRing R] [Algebra R B]
    [SMulCommClass (L ≃ₐ[K] L) R B] {σ : L ≃ₐ[K] L} :
    IsArithFrobAt R σ P ↔ ∃ hσ : σ ∈ A.decompositionSubgroup K,
      ∀ y : IsLocalRing.ResidueField A,
        (⟨σ, hσ⟩ : A.decompositionSubgroup K) • y = y ^ Nat.card (R ⧸ P.under R) := by
  have hiff := h.forall_smul_sub_pow_mem_iff (g := σ) (q := Nat.card (R ⧸ P.under R))
  refine ⟨fun hσ ↦ ⟨(h.decompositionSubgroup_eq (K := K)).ge hσ.mem_stabilizer,
    IsLocalRing.residue_surjective.forall.mpr fun x ↦ ?_⟩, fun ⟨hσ, hres⟩ ↦
    hiff.mpr fun x hx ↦ (residue_smul_eq_pow_iff A ⟨σ, hσ⟩ ⟨x, hx⟩ _).mp ?_⟩
  · rw [← IsLocalRing.ResidueField.residue_smul]
    exact (residue_smul_eq_pow_iff A _ x _).mpr (hiff.mp hσ x x.property)
  · rw [IsLocalRing.ResidueField.residue_smul]
    exact hres _

end IsCenteredAt

end ValuationSubring
