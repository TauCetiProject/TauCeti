/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.Map
public import TauCeti.NumberTheory.RamificationInertia.DoubleCoset.Basic

/-!
# Naturality of the double-coset splitting law

Let `M / K` be a finite Galois extension, let `Q` be a prime of `𝓞 M` above a prime `p` of
`𝓞 K`, and let `H ≤ H'` be subgroups of `Gal(M/K)`.  The inclusion reverses on fixed fields,
so a prime of `M ^ H` contracts to a prime of `M ^ H'`.  This file proves that this contraction
agrees with the canonical map

`H \ Gal(M/K) / D(Q) → H' \ Gal(M/K) / D(Q)`

under the double-coset splitting equivalences.  Thus the parametrization of primes by double
cosets is functorial as the intermediate field shrinks.

## Main definitions

* `Ideal.primesOverFixedFieldMap`: contraction from the primes over `p` in `M ^ H` to those in
  `M ^ H'`.

## Main results

* `Ideal.doubleCosetQuotientEquivPrimesOver_natural`: the naturality square between the quotient
  map and contraction commutes.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9.
* G. J. Janusz, *Algebraic Number Fields*, Chapter I.
-/

public section

open IntermediateField MulAction NumberField

open scoped NumberField Pointwise

namespace Ideal

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

omit [NumberField K] [NumberField M] in
/-- Contract a prime over `p` from the fixed field of `H` to the fixed field of a larger subgroup
`H'`.  The inclusion `H ≤ H'` gives the reverse inclusion `M ^ H' ⊆ M ^ H`. -/
noncomputable def primesOverFixedFieldMap (p : Ideal (𝓞 K))
    {H H' : Subgroup (M ≃ₐ[K] M)} (h : H ≤ H') :
    p.primesOver (𝓞 ↥(fixedField H)) → p.primesOver (𝓞 ↥(fixedField H')) := by
  letI : Algebra ↥(fixedField H') ↥(fixedField H) :=
    (IntermediateField.inclusion (fixedField_le h)).toAlgebra
  letI : IsScalarTower K ↥(fixedField H') ↥(fixedField H) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact fun q ↦
    ⟨q.1.under (𝓞 ↥(fixedField H')), inferInstance,
      ⟨by rw [under_under]; exact q.2.2.over⟩⟩

omit [NumberField K] [NumberField M] in
/-- `primesOverFixedFieldMap` is contraction of the underlying ideal. -/
@[simp]
theorem primesOverFixedFieldMap_coe (p : Ideal (𝓞 K))
    {H H' : Subgroup (M ≃ₐ[K] M)} (h : H ≤ H') (q : p.primesOver (𝓞 ↥(fixedField H))) :
    (primesOverFixedFieldMap p h q : Ideal (𝓞 ↥(fixedField H'))) =
      q.1.comap (NumberField.RingOfIntegers.mapRingHom
        (IntermediateField.inclusion (fixedField_le h))) :=
  (rfl)

omit [NumberField K] [NumberField M] in
/-- Contracting along the reflexive inclusion of a subgroup does not change a prime. -/
@[simp]
theorem primesOverFixedFieldMap_refl (p : Ideal (𝓞 K)) (H : Subgroup (M ≃ₐ[K] M)) :
    primesOverFixedFieldMap p (le_refl H) = id := by
  funext q
  apply Subtype.ext
  ext x
  simp only [primesOverFixedFieldMap_coe, mem_comap, IntermediateField.inclusion_self, id_eq]
  have hx : NumberField.RingOfIntegers.mapRingHom
      ((AlgHom.id K ↥(fixedField H)) : ↥(fixedField H) →+* ↥(fixedField H)) x = x := by
    apply NumberField.RingOfIntegers.ext
    simp
  rw [hx]

omit [NumberField K] [NumberField M] in
/-- Contraction between fixed fields composes along inclusions of subgroups. -/
theorem primesOverFixedFieldMap_trans (p : Ideal (𝓞 K))
    {H H' H'' : Subgroup (M ≃ₐ[K] M)} (h : H ≤ H') (h' : H' ≤ H'') :
    primesOverFixedFieldMap p (h.trans h') =
      primesOverFixedFieldMap p h' ∘ primesOverFixedFieldMap p h := by
  funext q
  apply Subtype.ext
  ext x
  simp only [primesOverFixedFieldMap_coe, Function.comp_apply, mem_comap]
  have hx : NumberField.RingOfIntegers.mapRingHom
      ((IntermediateField.inclusion (fixedField_le (h.trans h'))) :
        ↥(fixedField H'') →+* ↥(fixedField H)) x =
        NumberField.RingOfIntegers.mapRingHom
          ((IntermediateField.inclusion (fixedField_le h)) :
            ↥(fixedField H') →+* ↥(fixedField H))
          (NumberField.RingOfIntegers.mapRingHom
            ((IntermediateField.inclusion (fixedField_le h')) :
              ↥(fixedField H'') →+* ↥(fixedField H')) x) := by
    apply NumberField.RingOfIntegers.ext
    simp
  rw [hx]

private theorem doubleCosetQuotientEquivPrimesOver_natural_mk [IsGalois K M]
    (p : Ideal (𝓞 K))
    (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver p]
    {H H' : Subgroup (M ≃ₐ[K] M)} (h : H ≤ H') (σ : M ≃ₐ[K] M) :
    doubleCosetQuotientEquivPrimesOver p Q H'
        (DoubleCoset.quotientMapOfLELeft h (stabilizer (M ≃ₐ[K] M) Q)
          (DoubleCoset.mk H (stabilizer (M ≃ₐ[K] M) Q) σ)) =
      primesOverFixedFieldMap p h
        (doubleCosetQuotientEquivPrimesOver p Q H
          (DoubleCoset.mk H (stabilizer (M ≃ₐ[K] M) Q) σ)) := by
  let _ : Algebra ↥(fixedField H') ↥(fixedField H) :=
    (IntermediateField.inclusion (fixedField_le h)).toAlgebra
  let _ : IsScalarTower K ↥(fixedField H') ↥(fixedField H) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower ↥(fixedField H') ↥(fixedField H) M :=
    IsScalarTower.of_algebraMap_eq' rfl
  apply Subtype.ext
  simp only [DoubleCoset.quotientMapOfLELeft_apply_mk,
    doubleCosetQuotientEquivPrimesOver_mk, primesOverFixedFieldMap_coe]
  exact (under_under (A := 𝓞 ↥(fixedField H')) (B := 𝓞 ↥(fixedField H)) (σ • Q)).symm

/-- **Naturality of the double-coset splitting law.**  Enlarging `H` to `H'` on the
double-coset side agrees with contracting the corresponding prime from `M ^ H` to `M ^ H'`. -/
theorem doubleCosetQuotientEquivPrimesOver_natural [IsGalois K M] (p : Ideal (𝓞 K))
    (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver p]
    {H H' : Subgroup (M ≃ₐ[K] M)} (h : H ≤ H') :
    doubleCosetQuotientEquivPrimesOver p Q H' ∘
        DoubleCoset.quotientMapOfLELeft h (stabilizer (M ≃ₐ[K] M) Q) =
      primesOverFixedFieldMap p h ∘ doubleCosetQuotientEquivPrimesOver p Q H := by
  funext q
  induction q using Quotient.inductionOn' with
  | h σ => exact doubleCosetQuotientEquivPrimesOver_natural_mk p Q h σ

end Ideal
