/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RayClassField
public import TauCeti.NumberTheory.NumberField.Global.Ideles.IdealExtension

import TauCeti.FieldTheory.IntermediateField.ScalarTower
import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.HilbertTower
import TauCeti.NumberTheory.ClassFieldTheory.Global.PrincipalIdeal
import TauCeti.NumberTheory.NumberField.InfinitePlace.Transport
import TauCeti.RingTheory.Unramified.Equiv

/-!
# The principal ideal theorem

Every ideal of the ring of integers of a number field `K` becomes principal in the ring of
integers of its Hilbert class field `H = hilbertClassField K`.

## Strategy

By `ClassFields/HilbertTower`, the second Hilbert class field `secondHilbertClassField K` is a
Galois, everywhere-unramified finite extension of `K` containing `H`, whose norm group over `H` is
the trivial-modulus ray subgroup of `H` (`range_ideleClassNormMap_secondHilbertClassField`).

The idelic transfer theorem (`ideleClassExtension_mem_range_ideleClassNormMap_of_unramified`) then
shows that every idele class of `K`, extended to `H`, is a norm from `secondHilbertClassField K`,
and therefore lies in the trivial-modulus ray subgroup of `H`
(`ideleClassExtension_mem_raySubgroup_hilbertClassField`). By
`GlobalNumberFields.extendedHom_eq_one_iff_forall_ideleClassExtension_mem_raySubgroup`, the
extension map `ClassGroup.extendedHom (𝓞 K) (𝓞 H)` is trivial
(`extendedHom_hilbertClassField_eq_one`), so every ideal of `𝓞 K` extends to a principal ideal of
`𝓞 H` (`isPrincipal_map_hilbertClassField`).

## Main results

* `TauCeti.ClassFieldTheory.ideleClassExtension_mem_range_ideleClassNormMap_of_unramified`: every
  idele class of `K`, extended to `hilbertClassField K`, is a norm from any everywhere-unramified
  finite Galois extension containing `hilbertClassField K`.
* `TauCeti.ClassFieldTheory.ideleClassExtension_mem_raySubgroup_hilbertClassField`: every idele
  class of `K`, extended to `hilbertClassField K`, lies in the trivial-modulus ray subgroup.
* `TauCeti.ClassFieldTheory.extendedHom_hilbertClassField_eq_one`: extension of ideal classes
  from `𝓞 K` to `𝓞 (hilbertClassField K)` is trivial.
* `TauCeti.ClassFieldTheory.isPrincipal_map_hilbertClassField`: **the principal ideal theorem** —
  every ideal of `𝓞 K` becomes principal in `𝓞 (hilbertClassField K)`.
* `TauCeti.ClassFieldTheory.isPrincipal_map_of_algHom_hilbertClassField`,
  `TauCeti.ClassFieldTheory.isPrincipal_map_rayClassField`: principality in any field extension
  into which `hilbertClassField K` embeds over `K`, and in every ray class field of `K`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIII (The Principal Ideal Theorem).
* J. S. Milne, *Class Field Theory*, v4.03, Chapter V, Theorem 3.17.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §7 (Theorem 7.6).
-/

public noncomputable section

open IntermediateField IsDedekindDomain NumberField TauCeti.GlobalNumberFields
open scoped nonZeroDivisors

namespace TauCeti.ClassFieldTheory

/-! ### The principal ideal theorem -/

/-- Every idele class of `K`, extended to its Hilbert class field, is a norm from any
everywhere-unramified finite Galois extension containing that field. The relative algebra
and scalar tower are the caller's compatible choices. -/
theorem ideleClassExtension_mem_range_ideleClassNormMap_of_unramified
    {K : Type} [Field K] [NumberField K]
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
    [Algebra (hilbertClassField K) (classField K V)]
    [IsScalarTower (hilbertClassField K) (classField K V) (SeparableClosure K)]
    (hur : ∀ w : HeightOneSpectrum (𝓞 (classField K V)),
      Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    [IsUnramifiedAtInfinitePlaces K (classField K V)]
    (c : IdeleClassGroup (𝓞 K) K) :
    ideleClassExtension K (hilbertClassField K) c ∈
      (ideleClassNormMap (hilbertClassField K) (classField K V) :
        IdeleClassGroup (𝓞 (classField K V)) (classField K V) →*
          IdeleClassGroup (𝓞 (hilbertClassField K)) (hilbertClassField K)).range :=
  ideleClassExtension_mem_range_ideleClassNormMap_commutator_ofOpenNormal V
    (fixedField_commutator_eq_hilbertClassField V
      IntermediateField.le_of_isScalarTower hur)
    (fixedField_top_ofOpenNormal_eq_classField V) c

/-- **Idelic principal ideal theorem.** Every idele class of a number field `K`, extended to its
Hilbert class field `H`, lies in the trivial-modulus ray subgroup of `H`. -/
theorem ideleClassExtension_mem_raySubgroup_hilbertClassField (K : Type) [Field K]
    [NumberField K] (c : IdeleClassGroup (𝓞 K) K) :
    ideleClassExtension K (hilbertClassField K) c ∈
      raySubgroup (Modulus.one (hilbertClassField K)) := by
  let V := fixingOpenNormalSubgroup K (secondHilbertClassField K)
  have hV : classField K V = secondHilbertClassField K := by
    simpa only [IntermediateField.fieldRange_val] using
      classField_fixingOpenNormalSubgroup (secondHilbertClassField K).val
  have hHV : hilbertClassField K ≤ classField K V :=
    hV ▸ hilbertClassField_le_secondHilbertClassField K
  let : Algebra (hilbertClassField K) (classField K V) :=
    (IntermediateField.inclusion hHV).toAlgebra
  have : IsScalarTower (hilbertClassField K) (classField K V) (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let eVK : classField K V ≃ₐ[K] secondHilbertClassField K := IntermediateField.equivOfEq hV
  let eVH : classField K V ≃ₐ[hilbertClassField K] secondHilbertClassField K :=
    AlgEquiv.ofRingEquiv (f := eVK.toRingEquiv) fun _ ↦ Subtype.ext rfl
  have hur : ∀ w : HeightOneSpectrum (𝓞 (classField K V)),
      Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := fun w ↦ by
    let eO : 𝓞 (secondHilbertClassField K) ≃ₐ[𝓞 K] 𝓞 (classField K V) :=
      RingOfIntegers.mapAlgEquiv eVK.symm
    exact (AlgEquiv.isUnramifiedAt_iff_of_eq_comap eO rfl).1
      (isUnramifiedAt_secondHilbertClassField K
        (HeightOneSpectrum.comap eO.toRingEquiv.toRingHom eO.surjective w))
  have : IsUnramifiedAtInfinitePlaces K (classField K V) :=
    IsUnramifiedAtInfinitePlaces.of_equiv_equiv (RingEquiv.refl K) eVK.symm.toRingEquiv
      (RingHom.ext fun x ↦ (eVK.symm.commutes x).symm)
  have hmem := ideleClassExtension_mem_range_ideleClassNormMap_of_unramified V hur c
  rwa [range_ideleClassNormMap_eq_of_algEquiv eVH,
    range_ideleClassNormMap_secondHilbertClassField K] at hmem

/-- **The principal ideal theorem, class-group form.** Extension of ideal classes from `𝓞 K` to
the ring of integers of the Hilbert class field of `K` is the trivial homomorphism. -/
theorem extendedHom_hilbertClassField_eq_one (K : Type) [Field K] [NumberField K] :
    ClassGroup.extendedHom (𝓞 K) (𝓞 (hilbertClassField K)) = 1 :=
  extendedHom_eq_one_iff_forall_ideleClassExtension_mem_raySubgroup.2
    (ideleClassExtension_mem_raySubgroup_hilbertClassField K)

/-- **The principal ideal theorem** (Artin–Tate, *Class Field Theory*, Chapter XIII; Neukirch,
*Algebraic Number Theory*, Chapter VI, §7). Every ideal of `𝓞 K` becomes principal in the ring of
integers of the Hilbert class field of `K`. -/
theorem isPrincipal_map_hilbertClassField (K : Type) [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) :
    (I.map (algebraMap (𝓞 K) (𝓞 (hilbertClassField K)))).IsPrincipal := by
  by_cases hI : I = ⊥
  · subst hI
    rw [Ideal.map_bot]
    infer_instance
  · have hI0 : I ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero hI
    have h1 : ClassGroup.extendedHom (𝓞 K) (𝓞 (hilbertClassField K))
        (ClassGroup.mk0 ⟨I, hI0⟩) = 1 := by
      rw [extendedHom_hilbertClassField_eq_one K, MonoidHom.one_apply]
    rw [ClassGroup.extendedHom_mk0, ClassGroup.mk0_eq_one_iff] at h1
    exact h1

/-- **Principality in any extension containing the Hilbert class field.** If `L/K` is a field
extension into which the Hilbert class field of `K` embeds over `K`, then every ideal of `𝓞 K`
becomes principal in `𝓞 L`. -/
theorem isPrincipal_map_of_algHom_hilbertClassField {K : Type} [Field K] [NumberField K]
    {L : Type*} [Field L] [Algebra K L] (ι : hilbertClassField K →ₐ[K] L) (I : Ideal (𝓞 K)) :
    (I.map (algebraMap (𝓞 K) (𝓞 L))).IsPrincipal := by
  let φ : 𝓞 (hilbertClassField K) →ₐ[𝓞 K] 𝓞 L := RingOfIntegers.mapAlgHom ι
  have h := (isPrincipal_map_hilbertClassField K I).map_ringHom
    (φ : 𝓞 (hilbertClassField K) →+* 𝓞 L)
  rwa [Ideal.map_map, φ.comp_algebraMap] at h

/-- Every ideal of `𝓞 K` becomes principal in the ring of integers of every ray class field of `K`,
and in particular in the narrow Hilbert class field of `K`. -/
theorem isPrincipal_map_rayClassField {K : Type} [Field K] [NumberField K]
    (𝔪 : Modulus K) (I : Ideal (𝓞 K)) :
    (I.map (algebraMap (𝓞 K) (𝓞 (rayClassField 𝔪)))).IsPrincipal :=
  isPrincipal_map_of_algHom_hilbertClassField
    (IntermediateField.inclusion (hilbertClassField_le_rayClassField 𝔪)) I

end TauCeti.ClassFieldTheory
