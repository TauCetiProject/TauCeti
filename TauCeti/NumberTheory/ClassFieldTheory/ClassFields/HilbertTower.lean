/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RayClassField
public import TauCeti.NumberTheory.ClassFieldTheory.Global.PrincipalIdeal
import TauCeti.FieldTheory.IntermediateField.ScalarTower

/-!
# The maximal abelian subfield of an unramified extension

Let `L/K` be a finite Galois extension of number fields that is unramified at every finite
and infinite place and contains the Hilbert class field `H` of `K`. Its maximal abelian
subextension is exactly `H`: every abelian subextension is unramified and so lies in `H`,
while `H` itself is abelian.

`fixedField_commutator_eq_hilbertClassField` gives this identification in the finite-layer
presentation used by transfer. Consequently every idele class of `K`, extended to `H`, is a
norm from `L` (`ideleClassExtension_mem_range_ideleClassNormMap_of_unramified`).

The result applies to an unramified Galois extension containing `H`; it does not assert that
the Hilbert class field of `H` is Galois over `K`, or identify its norm group over `H`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIII.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §§6–7.
-/

public noncomputable section

open IntermediateField NumberField IsDedekindDomain

namespace TauCeti.ClassFieldTheory

open GlobalNumberFields

variable {K : Type} [Field K] [NumberField K]

/-- The maximal abelian subextension of an everywhere-unramified finite Galois extension
containing the Hilbert class field is the Hilbert class field itself. -/
theorem classField_maximalAbelianLayer_eq_hilbertClassField
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
    (hH : hilbertClassField K ≤ classField K V)
    (hur : ∀ w : HeightOneSpectrum (𝓞 (classField K V)),
      Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    [IsUnramifiedAtInfinitePlaces K (classField K V)] :
    classField K V.maximalAbelianLayer = hilbertClassField K := by
  let M := classField K V.maximalAbelianLayer
  have hML : M ≤ classField K V :=
    (classField_le_classField_iff K V V.maximalAbelianLayer).2 V.le_maximalAbelianLayer
  let : Algebra M (classField K V) := (IntermediateField.inclusion hML).toAlgebra
  have : IsScalarTower K M (classField K V) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsAbelianGalois K M :=
    isAbelianGalois_classField_iff.2 V.isAbelianClassFieldLayer_maximalAbelianLayer
  apply le_antisymm
  · have hMinf : IsUnramifiedAtInfinitePlaces K M :=
      IsUnramifiedAtInfinitePlaces.bot K M (classField K V)
    have hMfin (w : HeightOneSpectrum (𝓞 M)) :
        Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := by
      obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (w.asIdeal.primesOver (𝓞 (classField K V))))
      have : Algebra.IsUnramifiedAt (𝓞 K) Q :=
        hur ⟨Q, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot w.ne_bot Q⟩
      exact Algebra.IsUnramifiedAt.of_liesOver (𝓞 K) w.asIdeal Q
    simpa only [fieldRange_val] using
      (fieldRange_le_hilbertClassField_iff M.val).2 ⟨hMfin, hMinf⟩
  · rw [hilbertClassField, rayClassField_def] at hH ⊢
    exact (classField_le_classField_iff K V.maximalAbelianLayer _).2
      (OpenNormalSubgroup.maximalAbelianLayer_le
        ((classField_le_classField_iff K V _).1 hH)
        (globalClassField (rayNormSubgroup (Modulus.one K))).2)

/-- In an everywhere-unramified finite Galois extension containing the Hilbert class field,
the preimage of the finite Galois group's commutator fixes exactly the Hilbert class field.
This is the field identification required by the idelic transfer theorem. -/
theorem fixedField_commutator_eq_hilbertClassField
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
    (hH : hilbertClassField K ≤ classField K V)
    (hur : ∀ w : HeightOneSpectrum (𝓞 (classField K V)),
      Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    [IsUnramifiedAtInfinitePlaces K (classField K V)] :
    fixedField ((NormalLayer.ofOpenNormal V).subgroupLayer
      (commutator (NormalLayer.ofOpenNormal V).Gal)).ground.toSubgroup = hilbertClassField K := by
  rw [NormalLayer.ground_subgroupLayer, V.subgroupGround_commutator]
  have hfield : fixedField V.maximalAbelianLayer.toSubgroup =
      classField K V.maximalAbelianLayer := by
    simpa only [NormalLayer.top_ofOpenNormal] using
      fixedField_top_ofOpenNormal_eq_classField V.maximalAbelianLayer
  rw [hfield]
  exact classField_maximalAbelianLayer_eq_hilbertClassField V hH hur

/-- Every idele class of `K`, extended to its Hilbert class field, is a norm from any
everywhere-unramified finite Galois extension containing that field. The relative algebra
and scalar tower are the caller's compatible choices. -/
theorem ideleClassExtension_mem_range_ideleClassNormMap_of_unramified
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

end TauCeti.ClassFieldTheory
