/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RayClassField
public import TauCeti.NumberTheory.ClassFieldTheory.Global.PrincipalIdeal
import TauCeti.FieldTheory.Galois.Abelian.Basic
import TauCeti.FieldTheory.IntermediateField.ScalarTower
import TauCeti.FieldTheory.IsSepClosed
import TauCeti.NumberTheory.NumberField.InfinitePlace.Transport
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Transport
import TauCeti.RingTheory.Unramified.AlgEquiv
import TauCeti.RingTheory.Unramified.RingEquiv

/-!
# Hilbert class field towers and the second Hilbert class field

Let `L/K` be a finite Galois extension of number fields that is unramified at every finite
and infinite place and contains the Hilbert class field `H` of `K`. Its maximal abelian
subextension is exactly `H`: every abelian subextension is unramified and so lies in `H`,
while `H` itself is abelian.

`fixedField_commutator_eq_hilbertClassField` gives this identification in the finite-layer
presentation used by transfer. Consequently every idele class of `K`, extended to `H`, is a
norm from `L` (`ideleClassExtension_mem_range_ideleClassNormMap_of_unramified`).

This module also realizes the Hilbert class field of `H = hilbertClassField K` inside `Kˢ` as
the **second Hilbert class field** `secondHilbertClassField K`, proves that it is Galois and
everywhere unramified over `K`, and identifies its norm group over `H` with the trivial-modulus
ray subgroup of `H`.

## Main definitions

* `TauCeti.ClassFieldTheory.secondHilbertClassField`: the Hilbert class field of
  `hilbertClassField K`, realized as an intermediate field of `Kˢ / K`.

## Main results

* `TauCeti.ClassFieldTheory.fixedField_commutator_eq_hilbertClassField`: the commutator subgroup
  fixes `hilbertClassField K` in an everywhere-unramified finite Galois extension containing it.
* `TauCeti.ClassFieldTheory.ideleClassExtension_mem_range_ideleClassNormMap_of_unramified`: every
  idele class of `K`, extended to `hilbertClassField K`, is a norm from any everywhere-unramified
  finite Galois extension containing `hilbertClassField K`.
* `TauCeti.ClassFieldTheory.hilbertClassField_le_secondHilbertClassField`: `H ≤ H₂`.
* `TauCeti.ClassFieldTheory.le_secondHilbertClassField_of_unramified`: `secondHilbertClassField K`
  contains every everywhere-unramified finite abelian extension of `hilbertClassField K` in `Kˢ`.
* `TauCeti.ClassFieldTheory.isGalois_secondHilbertClassField`: `secondHilbertClassField K` is
  Galois over `K`.
* `TauCeti.ClassFieldTheory.isUnramifiedAt_secondHilbertClassField`,
  `TauCeti.ClassFieldTheory.isUnramifiedAtInfinitePlaces_secondHilbertClassField`:
  `secondHilbertClassField K` is unramified over `K` at every finite and infinite place.
* `TauCeti.ClassFieldTheory.range_ideleClassNormMap_secondHilbertClassField`: the norm group of
  `secondHilbertClassField K` over `hilbertClassField K` is the trivial-modulus ray subgroup.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIII.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §§6–7.
-/

public noncomputable section

open IntermediateField NumberField IsDedekindDomain

namespace TauCeti.ClassFieldTheory

open GlobalNumberFields

section MaximalAbelianLayer

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

end MaximalAbelianLayer

/-! ### Realizing the Hilbert class field of a subextension inside `Kˢ` -/

section HilbertClassFieldIn

variable (K H : Type) [Field K] [Field H] [NumberField H]
  [Algebra K H] [Algebra H (SeparableClosure K)] [IsScalarTower K H (SeparableClosure K)]

/-- Realize `hilbertClassField H` inside `Kˢ` via an `H`-embedding. Parameterizing over an
abstract base `H` avoids nested `IntermediateField` algebra synthesis when `H` is itself an
intermediate field of `Kˢ / K`. -/
private def hilbertClassFieldIn : IntermediateField K (SeparableClosure K) :=
  (IsSepClosed.lift : hilbertClassField H →ₐ[H] SeparableClosure K).fieldRange.restrictScalars K

private theorem algebraMap_mem_hilbertClassFieldIn (x : H) :
    algebraMap H (SeparableClosure K) x ∈ hilbertClassFieldIn K H :=
  ⟨algebraMap H (hilbertClassField H) x, AlgHom.commutes _ x⟩

private theorem fieldRange_eq_hilbertClassFieldIn
    (ι : hilbertClassField H →ₐ[H] SeparableClosure K) :
    ι.fieldRange.restrictScalars K = hilbertClassFieldIn K H := by
  let ι₀ : hilbertClassField H →ₐ[H] SeparableClosure K := IsSepClosed.lift
  have : Normal H ι₀.fieldRange := Normal.of_algEquiv ι₀.equivFieldRange
  have hrange : ι.fieldRange = ι₀.fieldRange := by
    have h := (ι.comp ι₀.equivFieldRange.symm.toAlgHom).fieldRange_of_normal
    rw [← AlgHom.map_fieldRange, AlgEquiv.fieldRange_eq_top, ← AlgHom.fieldRange_eq_map] at h
    exact h
  exact congrArg (IntermediateField.restrictScalars K) hrange

private def algEquivHilbertClassFieldIn
    (L : IntermediateField K (SeparableClosure K)) (hL : L = hilbertClassFieldIn K H)
    [Algebra H L] [IsScalarTower H L (SeparableClosure K)]
    (ι : hilbertClassField H →ₐ[H] SeparableClosure K) :
    hilbertClassField H ≃ₐ[H] L :=
  AlgEquiv.ofRingEquiv
    (f := ι.equivFieldRange.toRingEquiv.trans
      ((IntermediateField.restrictScalarsAlgEquiv K ι.fieldRange).symm.trans
        (IntermediateField.equivOfEq
          ((fieldRange_eq_hilbertClassFieldIn K H ι).trans hL.symm))).toRingEquiv)
    fun r ↦ Subtype.ext <| by
      simpa using (ι.commutes r).trans (IsScalarTower.algebraMap_apply H L (SeparableClosure K) r)

private theorem finiteDimensional_hilbertClassFieldIn
    (L : IntermediateField K (SeparableClosure K)) (hL : L = hilbertClassFieldIn K H)
    [Algebra H L] [IsScalarTower H L (SeparableClosure K)] :
    FiniteDimensional H L := by
  let e := algEquivHilbertClassFieldIn K H L hL IsSepClosed.lift
  exact Module.Finite.of_equiv_equiv (RingEquiv.refl H) e.toRingEquiv
    (RingHom.ext fun x ↦ (e.commutes x).symm)

private theorem isAbelianGalois_hilbertClassFieldIn
    (L : IntermediateField K (SeparableClosure K)) (hL : L = hilbertClassFieldIn K H)
    [Algebra H L] [IsScalarTower H L (SeparableClosure K)] :
    IsAbelianGalois H L := by
  let e := algEquivHilbertClassFieldIn K H L hL IsSepClosed.lift
  exact IsAbelianGalois.of_equiv_equiv (RingEquiv.refl H) e.toRingEquiv
    (RingHom.ext fun x ↦ (e.commutes x).symm)

private theorem isUnramifiedAt_hilbertClassFieldIn
    (L : IntermediateField K (SeparableClosure K)) (hL : L = hilbertClassFieldIn K H)
    [Algebra H L] [IsScalarTower H L (SeparableClosure K)]
    (w : HeightOneSpectrum (𝓞 L)) :
    Algebra.IsUnramifiedAt (𝓞 H) w.asIdeal := by
  let e := algEquivHilbertClassFieldIn K H L hL IsSepClosed.lift
  let eO : 𝓞 (hilbertClassField H) ≃ₐ[𝓞 H] 𝓞 L := RingOfIntegers.mapAlgEquiv e
  have hne : w.asIdeal.comap eO ≠ ⊥ :=
    mt (fun h ↦ by rw [← Ideal.map_comap_of_surjective eO eO.surjective w.asIdeal, h,
      Ideal.map_bot]) w.ne_bot
  exact (AlgEquiv.isUnramifiedAt_iff_of_eq_comap eO rfl).1
    (isUnramifiedAt_hilbertClassField H ⟨w.asIdeal.comap eO, inferInstance, hne⟩)

private theorem isUnramifiedAtInfinitePlaces_hilbertClassFieldIn
    (L : IntermediateField K (SeparableClosure K)) (hL : L = hilbertClassFieldIn K H)
    [Algebra H L] [IsScalarTower H L (SeparableClosure K)] :
    IsUnramifiedAtInfinitePlaces H L := by
  let e := algEquivHilbertClassFieldIn K H L hL IsSepClosed.lift
  exact IsUnramifiedAtInfinitePlaces.of_equiv_equiv (RingEquiv.refl H) e.toRingEquiv
    (RingHom.ext fun x ↦ (e.commutes x).symm)

private theorem range_ideleClassNormMap_hilbertClassFieldIn
    (L : IntermediateField K (SeparableClosure K)) (hL : L = hilbertClassFieldIn K H)
    [Algebra H L] [IsScalarTower H L (SeparableClosure K)] [NumberField L] :
    (ideleClassNormMap H L :
        IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 H) H).range =
      raySubgroup (Modulus.one H) := by
  rw [← range_ideleClassNormMap_rayClassField (Modulus.one H)]
  exact (range_ideleClassNormMap_eq_of_algEquiv
    (algEquivHilbertClassFieldIn K H L hL IsSepClosed.lift)).symm

private theorem le_hilbertClassFieldIn_of_unramified
    (E : IntermediateField K (SeparableClosure K))
    [Algebra H E] [IsScalarTower H E (SeparableClosure K)]
    [NumberField E] [IsAbelianGalois H E]
    (hfin : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 H) w.asIdeal)
    [IsUnramifiedAtInfinitePlaces H E] :
    E ≤ hilbertClassFieldIn K H := by
  have : IsSepClosure H (SeparableClosure K) :=
    TauCeti.isSepClosure_tower_top K H (SeparableClosure K)
  let Φ : SeparableClosure H ≃ₐ[H] SeparableClosure K :=
    IsSepClosure.equiv H (SeparableClosure H) (SeparableClosure K)
  let j : E →ₐ[H] SeparableClosure H :=
    Φ.symm.toAlgHom.comp (IsScalarTower.toAlgHom H E (SeparableClosure K))
  have hj : j.fieldRange ≤ hilbertClassField H :=
    (fieldRange_le_hilbertClassField_iff j).2 ⟨hfin, inferInstance⟩
  intro x hx
  have hmem : Φ.symm x ∈ hilbertClassField H := hj ⟨⟨x, hx⟩, rfl⟩
  rw [← fieldRange_eq_hilbertClassFieldIn K H (Φ.toAlgHom.comp (hilbertClassField H).val)]
  exact ⟨⟨Φ.symm x, hmem⟩, Φ.apply_symm_apply x⟩

end HilbertClassFieldIn

/-! ### The second Hilbert class field -/

/-- **The second Hilbert class field** of a number field `K`: the Hilbert class field of the
Hilbert class field `H` of `K`, realized as an intermediate field of `Kˢ / K`. -/
def secondHilbertClassField (K : Type) [Field K] [NumberField K] :
    IntermediateField K (SeparableClosure K) :=
  hilbertClassFieldIn K (hilbertClassField K)

section SecondHilbertClassField

variable (K : Type) [Field K] [NumberField K]

/-- The Hilbert class field of `K` lies in the second Hilbert class field of `K`. -/
theorem hilbertClassField_le_secondHilbertClassField :
    hilbertClassField K ≤ secondHilbertClassField K := fun x hx ↦
  algebraMap_mem_hilbertClassFieldIn K (hilbertClassField K) ⟨x, hx⟩

/-- The canonical inclusion makes `secondHilbertClassField K` an algebra over
`hilbertClassField K`. -/
instance instAlgebraHilbertClassFieldSecondHilbertClassField :
    Algebra (hilbertClassField K) (secondHilbertClassField K) :=
  (IntermediateField.inclusion (hilbertClassField_le_secondHilbertClassField K)).toAlgebra

/-- The scalar tower `K ⊆ hilbertClassField K ⊆ secondHilbertClassField K`. -/
instance instIsScalarTowerHilbertClassFieldSecondHilbertClassField :
    IsScalarTower K (hilbertClassField K) (secondHilbertClassField K) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The scalar tower `hilbertClassField K ⊆ secondHilbertClassField K ⊆ Kˢ`. -/
instance instIsScalarTowerSecondHilbertClassFieldSeparableClosure :
    IsScalarTower (hilbertClassField K) (secondHilbertClassField K) (SeparableClosure K) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The second Hilbert class field of `K` is finite over `hilbertClassField K`. -/
instance finiteDimensional_secondHilbertClassField_over_hilbertClassField :
    FiniteDimensional (hilbertClassField K) (secondHilbertClassField K) :=
  finiteDimensional_hilbertClassFieldIn K (hilbertClassField K) (secondHilbertClassField K) rfl

/-- The second Hilbert class field of `K` is finite over `K`. -/
instance finiteDimensional_secondHilbertClassField :
    FiniteDimensional K (secondHilbertClassField K) :=
  Module.Finite.trans (hilbertClassField K) (secondHilbertClassField K)

/-- The second Hilbert class field of `K` is a number field. -/
instance numberField_secondHilbertClassField : NumberField (secondHilbertClassField K) :=
  NumberField.of_module_finite K _

/-- The second Hilbert class field of `K` is abelian Galois over `hilbertClassField K`. -/
instance isAbelianGalois_secondHilbertClassField_over_hilbertClassField :
    IsAbelianGalois (hilbertClassField K) (secondHilbertClassField K) :=
  isAbelianGalois_hilbertClassFieldIn K (hilbertClassField K) (secondHilbertClassField K) rfl

/-- The second Hilbert class field of `K` is unramified over `hilbertClassField K` at every finite
prime. -/
theorem isUnramifiedAt_secondHilbertClassField_over_hilbertClassField
    (w : HeightOneSpectrum (𝓞 (secondHilbertClassField K))) :
    Algebra.IsUnramifiedAt (𝓞 (hilbertClassField K)) w.asIdeal :=
  isUnramifiedAt_hilbertClassFieldIn K (hilbertClassField K) (secondHilbertClassField K) rfl w

/-- The second Hilbert class field of `K` is unramified over `hilbertClassField K` at every
infinite place. -/
instance isUnramifiedAtInfinitePlaces_secondHilbertClassField_over_hilbertClassField :
    IsUnramifiedAtInfinitePlaces (hilbertClassField K) (secondHilbertClassField K) :=
  isUnramifiedAtInfinitePlaces_hilbertClassFieldIn K (hilbertClassField K)
    (secondHilbertClassField K) rfl

/-- **The second Hilbert class field is unramified over `K` at every finite prime.** -/
theorem isUnramifiedAt_secondHilbertClassField
    (w : HeightOneSpectrum (𝓞 (secondHilbertClassField K))) :
    Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := by
  let v := w.under (𝓞 (hilbertClassField K))
  have : Algebra.IsUnramifiedAt (𝓞 K) v.asIdeal := isUnramifiedAt_hilbertClassField K v
  have : Algebra.IsUnramifiedAt (𝓞 (hilbertClassField K)) w.asIdeal :=
    isUnramifiedAt_secondHilbertClassField_over_hilbertClassField K w
  exact Algebra.IsUnramifiedAt.comp v.asIdeal w.asIdeal

/-- **The second Hilbert class field is unramified over `K` at every infinite place.** -/
instance isUnramifiedAtInfinitePlaces_secondHilbertClassField :
    IsUnramifiedAtInfinitePlaces K (secondHilbertClassField K) :=
  IsUnramifiedAtInfinitePlaces.trans K (hilbertClassField K) (secondHilbertClassField K)

/-- **Maximality of the second Hilbert class field**: every everywhere-unramified finite abelian
extension of `hilbertClassField K` inside `Kˢ` lies in `secondHilbertClassField K`. -/
theorem le_secondHilbertClassField_of_unramified (E : IntermediateField K (SeparableClosure K))
    [Algebra (hilbertClassField K) E]
    [IsScalarTower (hilbertClassField K) E (SeparableClosure K)]
    [NumberField E] [IsAbelianGalois (hilbertClassField K) E]
    (hfin : ∀ w : HeightOneSpectrum (𝓞 E),
      Algebra.IsUnramifiedAt (𝓞 (hilbertClassField K)) w.asIdeal)
    [IsUnramifiedAtInfinitePlaces (hilbertClassField K) E] :
    E ≤ secondHilbertClassField K :=
  le_hilbertClassFieldIn_of_unramified K (hilbertClassField K) E hfin

/-- Every `K`-automorphism of `Kˢ` maps `secondHilbertClassField K` into itself: its image is
still an everywhere-unramified finite abelian extension of `hilbertClassField K`, so it lies in
`secondHilbertClassField K` by maximality. -/
private theorem map_secondHilbertClassField_le (σ : AbsoluteGaloisGroup K) :
    (secondHilbertClassField K).map σ.toAlgHom ≤ secondHilbertClassField K := by
  let H := hilbertClassField K
  let H₂ := secondHilbertClassField K
  let E := H₂.map σ.toAlgHom
  have hHmap : H.map σ.toAlgHom = H :=
    IntermediateField.normal_iff_forall_map_eq'.1 inferInstance σ
  have hHE : H ≤ E := by
    rw [← hHmap]
    exact IntermediateField.map_mono σ.toAlgHom (hilbertClassField_le_secondHilbertClassField K)
  let : Algebra H E := (IntermediateField.inclusion hHE).toAlgebra
  have : IsScalarTower K H E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower H E (SeparableClosure K) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- Transport abelianity and everywhere-unramifiedness from `H₂ / H` to `E / H` along `σ`.
  let f : H ≃+* H := (σ.restrictNormal H).toRingEquiv
  let g : H₂ ≃+* E := (H₂.equivMap σ.toAlgHom).toRingEquiv
  have hcomp : (algebraMap H E).comp (f : H →+* H) = (g : H₂ →+* E).comp (algebraMap H H₂) :=
    RingHom.ext fun x ↦ Subtype.ext (AlgEquiv.restrictNormal_commutes σ H x)
  have : FiniteDimensional H E := Module.Finite.of_equiv_equiv f g hcomp
  have : FiniteDimensional K E := Module.Finite.trans H E
  have : NumberField E := NumberField.of_module_finite K E
  have : IsAbelianGalois H E := IsAbelianGalois.of_equiv_equiv f g hcomp
  have : IsUnramifiedAtInfinitePlaces H E :=
    IsUnramifiedAtInfinitePlaces.of_equiv_equiv f g hcomp
  have hfin (w : HeightOneSpectrum (𝓞 E)) : Algebra.IsUnramifiedAt (𝓞 H) w.asIdeal := by
    let fO : 𝓞 H ≃+* 𝓞 H := RingOfIntegers.mapRingEquiv f
    let gO : 𝓞 H₂ ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv g
    have hcompO : (algebraMap (𝓞 H) (𝓞 E)).comp (fO : 𝓞 H →+* 𝓞 H) =
        (gO : 𝓞 H₂ →+* 𝓞 E).comp (algebraMap (𝓞 H) (𝓞 H₂)) :=
      RingHom.ext fun x ↦ RingOfIntegers.ext (RingHom.congr_fun hcomp (x : H))
    have hne : w.asIdeal.comap gO ≠ ⊥ :=
      (Ideal.comap_mapRingEquiv_eq_bot_iff w.asIdeal g).not.mpr w.ne_bot
    exact (Algebra.isUnramifiedAt_iff_of_equiv_equiv fO gO hcompO rfl).1
      (isUnramifiedAt_secondHilbertClassField_over_hilbertClassField K
        ⟨w.asIdeal.comap gO, inferInstance, hne⟩)
  exact le_secondHilbertClassField_of_unramified K E hfin

/-- **The second Hilbert class field of `K` is Galois over `K`.** -/
instance isGalois_secondHilbertClassField : IsGalois K (secondHilbertClassField K) where
  to_normal := IntermediateField.normal_iff_forall_map_le'.2 (map_secondHilbertClassField_le K)

/-- **The norm group of the second Hilbert class field over the Hilbert class field is the
trivial-modulus ray subgroup of the Hilbert class field.** -/
@[simp]
theorem range_ideleClassNormMap_secondHilbertClassField :
    (ideleClassNormMap (hilbertClassField K) (secondHilbertClassField K) :
        IdeleClassGroup (𝓞 (secondHilbertClassField K)) (secondHilbertClassField K) →*
          IdeleClassGroup (𝓞 (hilbertClassField K)) (hilbertClassField K)).range =
      raySubgroup (Modulus.one (hilbertClassField K)) :=
  range_ideleClassNormMap_hilbertClassFieldIn K (hilbertClassField K)
    (secondHilbertClassField K) rfl

end SecondHilbertClassField

end TauCeti.ClassFieldTheory
