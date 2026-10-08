/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.FixedField.FiberCount
public import TauCeti.NumberTheory.Chebotarev.SplitsCompletely
import TauCeti.NumberTheory.NumberField.Frobenius.FixedField.Inertia
import TauCeti.NumberTheory.NumberField.Frobenius.Tower

/-!
# The identity fibre in a cyclic fixed field

If a prime splits completely in a Galois extension, it also has residue degree one in every
intermediate field. Consequently its relative Frobenius in the extension over the fixed field of
an automorphism is the identity. This excludes the relative fibre of every nonidentity
automorphism, including a generator of a cyclic Galois group.

Conversely, when a nonidentity `σ` generates `Gal(L/K)`, no prime of `L ^ ⟨σ⟩` above a prime with
Artin class `[σ]` has trivial relative Frobenius: the relative identity fibre over such a prime is
empty (`fixedField_frobenius_fiber_one_eq_empty_of_generator`).

See J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
-/

public section

open IntermediateField
open scoped NumberField
open IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

-- `mem_frobeniusPrimeSet_iff` simplifies the fibres below before these equalities can apply,
-- so tagging them `@[simp]` would violate `simpNF`.
/-- Above a completely split prime, the relative Frobenius in `L/L ^ ⟨σ⟩` cannot be a
nonidentity `σ`. The statement uses the actual relative fibre, without identifying the fixed
field with `K` even when `σ` generates the whole Galois group. -/
theorem fixedField_frobenius_fiber_eq_empty_of_mem_frobeniusPrimeSet_one
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ frobeniusPrimeSet K L 1) :
    {P : HeightOneSpectrum (𝓞 ↥(fixedField (Subgroup.zpowers σ))) |
      P.under (𝓞 K) = p ∧
        P ∈ frobeniusPrimeSet ↥(fixedField (Subgroup.zpowers σ)) L
          (ConjClasses.mk σ.toFixedFieldAlgEquiv)} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro P ⟨hPp, hP⟩
  have hram : p ∉ ramifiedPrimes K L :=
    frobeniusPrimeSet_subset_compl_ramifiedPrimes (K := K) (L := L) 1 hp
  obtain ⟨Q, _⟩ := exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk hP
  have hQE : Q.1.under (𝓞 ↥(fixedField (Subgroup.zpowers σ))) = P.asIdeal := Q.2.2.over.symm
  have hQK : Q.1.under (𝓞 K) = p.asIdeal := by
    rw [← Ideal.under_under (B := 𝓞 ↥(fixedField (Subgroup.zpowers σ))) Q.1,
      hQE, ← HeightOneSpectrum.under_asIdeal, hPp]
  have : Q.1.LiesOver p.asIdeal := ⟨hQK.symm⟩
  have hQdeg : Q.1.inertiaDeg (𝓞 K) = 1 :=
    inertiaDeg_eq_one_of_mem_frobeniusPrimeSet_one hp Q.1
  have hPdeg : P.asIdeal.inertiaDeg (𝓞 K) = 1 := by
    have hdiv := Ideal.inertiaDeg_below_dvd (R := 𝓞 K)
      (Q.1.under (𝓞 ↥(fixedField (Subgroup.zpowers σ)))) Q.1
    rw [hQE, hQdeg] at hdiv
    exact Nat.dvd_one.mp hdiv
  have hpσ : p ∈ frobeniusPrimeSet K L (ConjClasses.mk σ) :=
    (inertiaDeg_eq_one_iff_under_mem_frobeniusPrimeSet σ hP
      (hPp ▸ hram)).mp hPdeg |> (hPp ▸ ·)
  have hne : (1 : ConjClasses (L ≃ₐ[K] L)) ≠ ConjClasses.mk σ := by
    intro hclass
    have hc : IsConj σ 1 := ConjClasses.mk_eq_mk_iff_isConj.mp
      (by simpa only [ConjClasses.one_eq_mk_one] using hclass.symm)
    exact hσ (isConj_one_left.mp hc)
  exact Set.disjoint_left.mp (disjoint_frobeniusPrimeSet hne) hp hpσ

/-- The fixed-field relative fibre of a nonidentity element over a completely split prime has
cardinality zero. When `σ` generates a nontrivial cyclic Galois group, this gives zero
cardinality over the identity Frobenius fibre. -/
theorem fixedField_frobenius_fiber_card_eq_zero_of_mem_frobeniusPrimeSet_one
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ frobeniusPrimeSet K L 1) :
    Nat.card {P : HeightOneSpectrum (𝓞 ↥(fixedField (Subgroup.zpowers σ))) //
      P.under (𝓞 K) = p ∧
        P ∈ frobeniusPrimeSet ↥(fixedField (Subgroup.zpowers σ)) L
          (ConjClasses.mk σ.toFixedFieldAlgEquiv)} = 0 := by
  have h := congrArg (fun s : Set (HeightOneSpectrum
      (𝓞 ↥(fixedField (Subgroup.zpowers σ)))) ↦ Nat.card s)
    (fixedField_frobenius_fiber_eq_empty_of_mem_frobeniusPrimeSet_one σ hσ p hp)
  exact h.trans (by simp)

/-- **The relative identity fibre over a generator-tagged prime is empty.** If a nonidentity `σ`
generates `Gal(L/K)` and `p` has Artin class `[σ]`, then no prime of `L ^ ⟨σ⟩` above `p` has
trivial relative Frobenius in `L / L ^ ⟨σ⟩`.

An absolute Frobenius `φ` at a prime `Q` of `L` above `p` lies in `⟨σ⟩ = Gal(L/K)`, so the prime of
`L ^ ⟨σ⟩` below `Q` has residue degree one over `K` and `φ` is also the relative Frobenius at `Q`.
If that were `1`, then `φ = 1` would be conjugate to `σ ≠ 1`. -/
theorem fixedField_frobenius_fiber_one_eq_empty_of_generator (σ : L ≃ₐ[K] L)
    (hσ : Subgroup.zpowers σ = ⊤) (hσ1 : σ ≠ 1) (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ frobeniusPrimeSet K L (ConjClasses.mk σ)) :
    {P : HeightOneSpectrum (𝓞 ↥(fixedField (Subgroup.zpowers σ))) |
      P.under (𝓞 K) = p ∧ P ∈ frobeniusPrimeSet ↥(fixedField (Subgroup.zpowers σ)) L 1} = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun P ⟨hPp, hP⟩ ↦ ?_
  rw [ConjClasses.one_eq_mk_one] at hP
  obtain ⟨hur, -⟩ := mem_frobeniusPrimeSet_iff.mp hp
  obtain ⟨Q, hQ1⟩ := exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk hP
  have : Q.1.IsPrime := Q.2.1
  have hQK : Q.1.under (𝓞 K) = p.asIdeal := by
    rw [← Ideal.under_under (B := 𝓞 ↥(fixedField (Subgroup.zpowers σ))) Q.1,
      ← Q.2.2.over, ← HeightOneSpectrum.under_asIdeal, hPp]
  have : Q.1.LiesOver p.asIdeal := ⟨hQK.symm⟩
  have hQ0 : Q.1 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot Q.1
  have : Algebra.IsUnramifiedAt (𝓞 K) Q.1 := hur Q.1
  have : Algebra.IsUnramifiedAt (𝓞 ↥(fixedField (Subgroup.zpowers σ))) Q.1 :=
    Algebra.IsUnramifiedAt.of_restrictScalars (𝓞 K) Q.1
  obtain ⟨φ, hφ⟩ := NumberField.exists_isArithFrobAt (K := K) Q.1 hQ0
  have hdeg : (Q.1.under (𝓞 ↥(fixedField (Subgroup.zpowers σ)))).inertiaDeg (𝓞 K) = 1 :=
    (Ideal.inertiaDeg_under_fixedField_eq_one_iff Q.1 hQ0 _ hφ).mpr (hσ ▸ Subgroup.mem_top φ)
  obtain ⟨τ, hτ, hτφ⟩ := NumberField.exists_isArithFrobAt_pow_inertiaDeg
    (fixedField (Subgroup.zpowers σ)) Q.1 _ p.asIdeal rfl hQK hur φ hφ
  have hφ1 : φ = 1 := by
    rw [hdeg, pow_one, NumberField.isArithFrobAt_eq_of_isUnramifiedAt hτ hQ1] at hτφ
    rw [← hτφ]
    rfl
  have hne : ConjClasses.mk (1 : L ≃ₐ[K] L) ≠ ConjClasses.mk σ := by
    rw [Ne, ConjClasses.mk_eq_mk_iff_isConj, isConj_one_right]
    exact hσ1
  exact Set.disjoint_left.mp (disjoint_frobeniusPrimeSet hne)
    (mem_frobeniusPrimeSet_mk_of_isArithFrobAt hur Q.1 (hφ1 ▸ hφ)) hp

end NumberField.Chebotarev
