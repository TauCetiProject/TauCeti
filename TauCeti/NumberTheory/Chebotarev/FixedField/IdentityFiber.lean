/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.FixedField.FiberCount
public import TauCeti.NumberTheory.Chebotarev.SplitsCompletely

/-!
# The identity fibre in a cyclic fixed field

If a prime splits completely in a Galois extension, it also has residue degree one in every
intermediate field. Consequently its relative Frobenius in the extension over the fixed field of
an automorphism is the identity. This excludes the relative fibre of every nonidentity
automorphism, including a generator of a cyclic Galois group.

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

end NumberField.Chebotarev
