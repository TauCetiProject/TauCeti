/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RayClassField
public import TauCeti.NumberTheory.ClassFieldTheory.Global.PrincipalIdeal
import TauCeti.FieldTheory.IntermediateField.ScalarTower
import TauCeti.NumberTheory.NumberField.AlgEquiv
import TauCeti.NumberTheory.NumberField.InfinitePlace.Transport

/-!
# The Hilbert class field tower in the separable closure

Let `L/K` be a finite Galois extension of number fields that is unramified at every finite
and infinite place and contains the Hilbert class field `H` of `K`. Its maximal abelian
subextension is exactly `H`: every abelian subextension is unramified and so lies in `H`,
while `H` itself is abelian.

`fixedField_commutator_eq_hilbertClassField` gives this identification in the finite-layer
presentation used by transfer. Consequently every idele class of `K`, extended to `H`, is a
norm from `L` (`ideleClassExtension_mem_range_ideleClassNormMap_of_unramified`,
`ideleClassExtension_mem_range_ideleClassNormMap_of_isGalois_of_unramified`).

To instantiate this at the second step of the Hilbert class field tower, we specialize
`rayClassFieldOver` (from `RayClassField.lean`) to the ordinary and narrow Hilbert class fields
of any number field `L` in a tower `K → L → Kˢ` inside `Kˢ` (`hilbertClassFieldOver`,
`narrowHilbertClassFieldOver`):

* They inherit the degree and universal-property characterizations of the ordinary and narrow
  Hilbert class fields (`finrank_hilbertClassFieldOver`, `finrank_narrowHilbertClassFieldOver`,
  `fieldRange_le_hilbertClassFieldOver_iff`, `fieldRange_le_narrowHilbertClassFieldOver_iff`).
* Unramifiedness lifts in the tower at finite primes
  (`isUnramifiedAt_hilbertClassFieldOver_tower_top`,
  `isUnramifiedAt_hilbertClassFieldOver_of_isUnramifiedAt`,
  `isUnramifiedAt_narrowHilbertClassFieldOver_tower_top`,
  `isUnramifiedAt_narrowHilbertClassFieldOver_of_isUnramifiedAt`) and at infinite places for the
  ordinary Hilbert tower (`isUnramifiedAtInfinitePlaces_hilbertClassFieldOver_tower_top`,
  `isUnramifiedAtInfinitePlaces_hilbertClassFieldOver`).
* When `L/K` is Galois, both `hilbertClassFieldOver K L` and `narrowHilbertClassFieldOver K L` are
  Galois over `K` (`isGalois_hilbertClassFieldOver`, `isGalois_narrowHilbertClassFieldOver`), via
  `isGalois_rayClassFieldOver_of_forall_isAdmissibleModulus` by transporting unramifiedness along
  automorphisms of `L/K`.

## Main definitions

* `hilbertClassFieldOver`, `narrowHilbertClassFieldOver`: the ordinary and narrow Hilbert class
  fields of `L` inside `SeparableClosure K`.

## Main results

* `ideleClassExtension_mem_range_ideleClassNormMap_of_isGalois_of_unramified`: extended idele
  classes in `hilbertClassField K` are norms from any everywhere-unramified finite Galois
  intermediate field containing `hilbertClassField K`.
* `finrank_hilbertClassFieldOver`, `finrank_narrowHilbertClassFieldOver`,
  `fieldRange_le_hilbertClassFieldOver_iff`, `fieldRange_le_narrowHilbertClassFieldOver_iff`:
  degree and universal-property characterizations of the relative (narrow) Hilbert class field.
* `isUnramifiedAt_hilbertClassFieldOver_of_isUnramifiedAt`,
  `isUnramifiedAtInfinitePlaces_hilbertClassFieldOver`: preservation of unramifiedness in the
  relative Hilbert class-field tower.
* `isGalois_hilbertClassFieldOver`, `isGalois_narrowHilbertClassFieldOver`: Galoisness over `K`
  when `L/K` is Galois.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIII.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §§6–7.
-/

public noncomputable section

open IntermediateField NumberField IsDedekindDomain

namespace TauCeti.ClassFieldTheory

open GlobalNumberFields

section Transfer

variable {K : Type} [Field K] [NumberField K]

/-! ### Maximal abelian subextension and transfer in unramified extensions -/

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
        (globalClassField (rayNormSubgroup (Modulus.one K))).property)

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

/-- Intermediate-field form of `ideleClassExtension_mem_range_ideleClassNormMap_of_unramified`:
every idele class of `K`, extended to `hilbertClassField K`, is a norm from any
everywhere-unramified finite Galois intermediate field `E` of `Kˢ / K` containing
`hilbertClassField K`. -/
theorem ideleClassExtension_mem_range_ideleClassNormMap_of_isGalois_of_unramified
    (E : IntermediateField K (SeparableClosure K)) [NumberField E]
    [IsGalois K E] [Algebra (hilbertClassField K) E]
    [IsScalarTower (hilbertClassField K) E (SeparableClosure K)]
    (hur : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    [IsUnramifiedAtInfinitePlaces K E]
    (c : IdeleClassGroup (𝓞 K) K) :
    ideleClassExtension K (hilbertClassField K) c ∈
      (ideleClassNormMap (hilbertClassField K) E :
        IdeleClassGroup (𝓞 E) E →*
          IdeleClassGroup (𝓞 (hilbertClassField K)) (hilbertClassField K)).range := by
  obtain ⟨V, rfl⟩ := (exists_classField_eq_iff E).2 ⟨inferInstance, inferInstance⟩
  exact ideleClassExtension_mem_range_ideleClassNormMap_of_unramified V hur c

end Transfer

/-! ### Relative Hilbert class fields in the separable closure of the base -/

section RelativeHilbertClassFields

variable (K : Type) [Field K]
  {L : Type} [Field L] [NumberField L] [Algebra K L]
  [Algebra L (SeparableClosure K)] [IsScalarTower K L (SeparableClosure K)]

variable (L) in
/-- **The Hilbert class field of `L`, realized inside `SeparableClosure K`.** -/
abbrev hilbertClassFieldOver : IntermediateField K (SeparableClosure K) :=
  rayClassFieldOver K (Modulus.one L)

variable (L) in
/-- **The narrow Hilbert class field of `L`, realized inside `SeparableClosure K`.** -/
abbrev narrowHilbertClassFieldOver : IntermediateField K (SeparableClosure K) :=
  rayClassFieldOver K (narrowModulus L)

variable (L) in
/-- **The degree of `hilbertClassFieldOver K L` over `L` is the class number of `L`.** -/
@[simp high]
theorem finrank_hilbertClassFieldOver
    [Algebra L (hilbertClassFieldOver K L)]
    [IsScalarTower L (hilbertClassFieldOver K L) (SeparableClosure K)] :
    Module.finrank L (hilbertClassFieldOver K L) = classNumber L := by
  obtain ⟨e⟩ := nonempty_algEquiv_rayClassFieldOver K (Modulus.one L)
  exact e.symm.toLinearEquiv.finrank_eq.trans (finrank_hilbertClassField L)

variable (L) in
/-- **The degree of `narrowHilbertClassFieldOver K L` over `L` is `#(NarrowClassGroup L)`.** -/
@[simp high]
theorem finrank_narrowHilbertClassFieldOver
    [Algebra L (narrowHilbertClassFieldOver K L)]
    [IsScalarTower L (narrowHilbertClassFieldOver K L) (SeparableClosure K)] :
    Module.finrank L (narrowHilbertClassFieldOver K L) = Nat.card (NarrowClassGroup L) := by
  obtain ⟨e⟩ := nonempty_algEquiv_rayClassFieldOver K (narrowModulus L)
  exact e.symm.toLinearEquiv.finrank_eq.trans (finrank_narrowHilbertClassField L)

variable {K} in
/-- **Universal property of `hilbertClassFieldOver K L`**: a finite abelian extension `M/L`
embedded in `SeparableClosure K` by `ι` lies in `hilbertClassFieldOver K L` if and only if `M/L`
is unramified at all finite and infinite places. -/
theorem fieldRange_le_hilbertClassFieldOver_iff
    {M : Type} [Field M] [NumberField M] [Algebra L M] [IsAbelianGalois L M]
    (ι : M →ₐ[L] SeparableClosure K) :
    ι.fieldRange.restrictScalars K ≤ hilbertClassFieldOver K L ↔
      (∀ w : HeightOneSpectrum (𝓞 M), Algebra.IsUnramifiedAt (𝓞 L) w.asIdeal) ∧
        IsUnramifiedAtInfinitePlaces L M := by
  rw [← isAdmissibleModulus_iff_le_rayClassFieldOver, isAdmissibleModulus_one_iff]

variable {K} in
/-- **Universal property of `narrowHilbertClassFieldOver K L`**: a finite abelian extension `M/L`
embedded in `SeparableClosure K` by `ι` lies in `narrowHilbertClassFieldOver K L` if and only if
`M/L` is unramified at every finite prime. -/
theorem fieldRange_le_narrowHilbertClassFieldOver_iff
    {M : Type} [Field M] [NumberField M] [Algebra L M] [IsAbelianGalois L M]
    (ι : M →ₐ[L] SeparableClosure K) :
    ι.fieldRange.restrictScalars K ≤ narrowHilbertClassFieldOver K L ↔
      ∀ w : HeightOneSpectrum (𝓞 M), Algebra.IsUnramifiedAt (𝓞 L) w.asIdeal := by
  rw [← isAdmissibleModulus_iff_le_rayClassFieldOver, isAdmissibleModulus_narrowModulus_iff]

variable (L) in
/-- Every prime of `hilbertClassFieldOver K L` is unramified over `𝓞 L`. -/
theorem isUnramifiedAt_hilbertClassFieldOver_tower_top
    [Algebra L (hilbertClassFieldOver K L)]
    [IsScalarTower L (hilbertClassFieldOver K L) (SeparableClosure K)]
    (w : HeightOneSpectrum (𝓞 (hilbertClassFieldOver K L))) :
    Algebra.IsUnramifiedAt (𝓞 L) w.asIdeal :=
  isUnramifiedAt_rayClassFieldOver_tower_top_of_notMem_support K (Modulus.one L) (by simp)

variable (L) in
/-- Every prime of `narrowHilbertClassFieldOver K L` is unramified over `𝓞 L`. -/
theorem isUnramifiedAt_narrowHilbertClassFieldOver_tower_top
    [Algebra L (narrowHilbertClassFieldOver K L)]
    [IsScalarTower L (narrowHilbertClassFieldOver K L) (SeparableClosure K)]
    (w : HeightOneSpectrum (𝓞 (narrowHilbertClassFieldOver K L))) :
    Algebra.IsUnramifiedAt (𝓞 L) w.asIdeal :=
  isUnramifiedAt_rayClassFieldOver_tower_top_of_notMem_support K (narrowModulus L) (by simp)

variable (L) in
/-- `hilbertClassFieldOver K L` is unramified over `L` at all infinite places. -/
instance isUnramifiedAtInfinitePlaces_hilbertClassFieldOver_tower_top
    [Algebra L (hilbertClassFieldOver K L)]
    [IsScalarTower L (hilbertClassFieldOver K L) (SeparableClosure K)] :
    IsUnramifiedAtInfinitePlaces L (hilbertClassFieldOver K L) :=
  (isAdmissibleModulus_one_iff.1 (isAdmissibleModulus_rayClassFieldOver K (Modulus.one L))).2

variable (L) in
/-- Any prime `w` of `hilbertClassFieldOver K L` lying over a prime of `𝓞 L` unramified over `𝓞 K`
is itself unramified over `𝓞 K`. -/
theorem isUnramifiedAt_hilbertClassFieldOver_of_isUnramifiedAt
    [Algebra L (hilbertClassFieldOver K L)]
    [IsScalarTower L (hilbertClassFieldOver K L) (SeparableClosure K)]
    {w : HeightOneSpectrum (𝓞 (hilbertClassFieldOver K L))}
    (hL : Algebra.IsUnramifiedAt (𝓞 K) (w.under (𝓞 L)).asIdeal) :
    Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
  isUnramifiedAt_rayClassFieldOver_of_notMem_support_of_isUnramifiedAt K (Modulus.one L)
    (by simp) hL

variable (L) in
/-- Any prime `w` of `narrowHilbertClassFieldOver K L` lying over a prime of `𝓞 L` unramified over
`𝓞 K` is itself unramified over `𝓞 K`. -/
theorem isUnramifiedAt_narrowHilbertClassFieldOver_of_isUnramifiedAt
    [Algebra L (narrowHilbertClassFieldOver K L)]
    [IsScalarTower L (narrowHilbertClassFieldOver K L) (SeparableClosure K)]
    {w : HeightOneSpectrum (𝓞 (narrowHilbertClassFieldOver K L))}
    (hL : Algebra.IsUnramifiedAt (𝓞 K) (w.under (𝓞 L)).asIdeal) :
    Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
  isUnramifiedAt_rayClassFieldOver_of_notMem_support_of_isUnramifiedAt K (narrowModulus L)
    (by simp) hL

variable (L) in
/-- If `L/K` is unramified at all infinite places, then so is `hilbertClassFieldOver K L / K`. -/
instance isUnramifiedAtInfinitePlaces_hilbertClassFieldOver [IsUnramifiedAtInfinitePlaces K L] :
    IsUnramifiedAtInfinitePlaces K (hilbertClassFieldOver K L) := by
  let _ := algebraRayClassFieldOver K (Modulus.one L)
  have := isScalarTower_left_rayClassFieldOver K (Modulus.one L)
  have := isScalarTower_right_rayClassFieldOver K (Modulus.one L)
  exact IsUnramifiedAtInfinitePlaces.trans K L (hilbertClassFieldOver K L)

variable (L) in
/-- **The Hilbert class field of a Galois subextension `L/K` is Galois over `K`.** Every conjugate
of `hilbertClassFieldOver K L` over `K` is an everywhere-unramified abelian extension of `L`, hence
lies in `hilbertClassFieldOver K L` by maximality of the Hilbert class field. -/
instance isGalois_hilbertClassFieldOver [IsGalois K L] :
    IsGalois K (hilbertClassFieldOver K L) :=
  isGalois_rayClassFieldOver_of_forall_isAdmissibleModulus K (Modulus.one L)
    fun f g hcomp ↦ isAdmissibleModulus_one_iff.mpr
      ⟨(RingEquiv.forall_heightOneSpectrum_ringOfIntegers_isUnramifiedAt_iff
          f.toRingEquiv g hcomp).mp (isUnramifiedAt_hilbertClassField L),
        IsUnramifiedAtInfinitePlaces.of_equiv_equiv f.toRingEquiv g hcomp⟩

variable (L) in
/-- **The narrow Hilbert class field of a Galois subextension `L/K` is Galois over `K`.** Every
conjugate of `narrowHilbertClassFieldOver K L` over `K` is an abelian extension of `L` unramified
at all finite primes, hence lies in `narrowHilbertClassFieldOver K L` by maximality of the narrow
Hilbert class field. -/
instance isGalois_narrowHilbertClassFieldOver [IsGalois K L] :
    IsGalois K (narrowHilbertClassFieldOver K L) :=
  isGalois_rayClassFieldOver_of_forall_isAdmissibleModulus K (narrowModulus L)
    fun f g hcomp ↦ isAdmissibleModulus_narrowModulus_iff.mpr <|
      (RingEquiv.forall_heightOneSpectrum_ringOfIntegers_isUnramifiedAt_iff
        f.toRingEquiv g hcomp).mp (isUnramifiedAt_narrowHilbertClassField L)

end RelativeHilbertClassFields

end TauCeti.ClassFieldTheory
