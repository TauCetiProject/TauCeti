/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RayClassField
public import TauCeti.NumberTheory.NumberField.Global.Ideles.IdealExtension

import TauCeti.FieldTheory.Galois.Abelian.Basic
import TauCeti.FieldTheory.IsSepClosed
import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.HilbertTower
import TauCeti.NumberTheory.NumberField.InfinitePlace.Transport
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Transport
import TauCeti.RingTheory.Unramified.AlgEquiv
import TauCeti.RingTheory.Unramified.RingEquiv

/-!
# The principal ideal theorem

Every ideal of the ring of integers of a number field `K` becomes principal in the ring of
integers of its Hilbert class field `H = hilbertClassField K`.

## Strategy

Realize the Hilbert class field of `H` inside `Kˢ` as the **second Hilbert class field**
`secondHilbertClassField K`. Because `hilbertClassField H` is normal over `H`, its image in `Kˢ`
does not depend on the choice of `H`-embedding, and it contains every everywhere-unramified finite
abelian extension of `H` inside `Kˢ` (`le_secondHilbertClassField_of_unramified`).

The key arithmetic input is that `secondHilbertClassField K` is Galois over `K`
(`isGalois_secondHilbertClassField`): any `σ ∈ Gal(Kˢ/K)` stabilizes `H`, so it carries
`secondHilbertClassField K` to an everywhere-unramified finite abelian extension of `H`, which
lies back inside `secondHilbertClassField K` by maximality. Since both steps `H/K` and `H₂/H` are
everywhere unramified, `H₂/K` is an everywhere-unramified finite Galois extension containing `H`.

The idelic transfer theorem (`ideleClassExtension_mem_range_ideleClassNormMap_of_unramified`) then
shows that every idele class of `K`, extended to `H`, is a norm from `H₂`, and therefore lies in
the trivial-modulus ray subgroup of `H` (`ideleClassExtension_mem_raySubgroup_hilbertClassField`).
By `GlobalNumberFields.extendedHom_eq_one_iff_forall_ideleClassExtension_mem_raySubgroup`, the
extension map `ClassGroup.extendedHom (𝓞 K) (𝓞 H)` is trivial
(`extendedHom_hilbertClassField_eq_one`), so every ideal of `𝓞 K` extends to a principal ideal of
`𝓞 H` (`isPrincipal_map_hilbertClassField`).

## Main definitions

* `TauCeti.ClassFieldTheory.secondHilbertClassField`: the Hilbert class field of the Hilbert
  class field of `K`, realized as an intermediate field of `Kˢ / K`.

## Main results

* `TauCeti.ClassFieldTheory.hilbertClassField_le_secondHilbertClassField`: `H ≤ H₂`.
* `TauCeti.ClassFieldTheory.le_secondHilbertClassField_of_unramified`: `secondHilbertClassField K`
  contains every everywhere-unramified finite abelian extension of `hilbertClassField K` in `Kˢ`.
* `TauCeti.ClassFieldTheory.isGalois_secondHilbertClassField`: the second Hilbert class field of
  `K` is Galois over `K`.
* `TauCeti.ClassFieldTheory.isUnramifiedAt_secondHilbertClassField`,
  `TauCeti.ClassFieldTheory.isUnramifiedAtInfinitePlaces_secondHilbertClassField`: the second
  Hilbert class field of `K` is unramified over `K` at every finite and infinite place.
* `TauCeti.ClassFieldTheory.range_ideleClassNormMap_secondHilbertClassField`: the norm group of
  `secondHilbertClassField K` over `hilbertClassField K` is the trivial-modulus ray subgroup.
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
  AlgEquiv.ofBijective
    { toFun x := ⟨ι x, by
        rw [hL, ← fieldRange_eq_hilbertClassFieldIn K H ι]
        exact ⟨x, rfl⟩⟩
      map_one' := Subtype.ext (map_one ι)
      map_mul' x y := Subtype.ext (map_mul ι x y)
      map_zero' := Subtype.ext (map_zero ι)
      map_add' x y := Subtype.ext (map_add ι x y)
      commutes' r := Subtype.ext <|
        (ι.commutes r).trans (IsScalarTower.algebraMap_apply H L (SeparableClosure K) r) }
    ⟨fun _ _ h ↦ ι.injective (congrArg Subtype.val h), fun ⟨_, hy⟩ ↦ by
      rw [hL, ← fieldRange_eq_hilbertClassFieldIn K H ι] at hy
      obtain ⟨x, rfl⟩ := hy
      exact ⟨x, rfl⟩⟩

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

/-! ### The principal ideal theorem -/

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
    have hne : w.asIdeal.comap eO ≠ ⊥ :=
      mt (fun h ↦ by rw [← Ideal.map_comap_of_surjective eO eO.surjective w.asIdeal, h,
        Ideal.map_bot]) w.ne_bot
    exact (AlgEquiv.isUnramifiedAt_iff_of_eq_comap eO rfl).1
      (isUnramifiedAt_secondHilbertClassField K ⟨w.asIdeal.comap eO, inferInstance, hne⟩)
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
