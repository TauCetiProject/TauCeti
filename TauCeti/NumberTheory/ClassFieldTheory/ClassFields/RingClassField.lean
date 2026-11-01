/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RingClassQuotient
public import TauCeti.NumberTheory.ClassFieldTheory.Global.AdmissibleModulus.Reciprocity
public import TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.Correspondence

import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# The ring class field of an order in a quadratic field

Let `O` be an order of conductor `𝔣` in a quadratic field `K`. The kernel of the idelic ring-class
quotient `ringClassIdeleQuotient O : C_K → Pic O` is an open subgroup of finite index of the idele
class group (`ringClassNormSubgroup O`), so the global class-field correspondence attaches to it a
unique finite abelian extension of `K` inside `Kˢ` with that norm group: the **ring class field**
`ringClassField O hK`. It is the class field of the value of `globalClassField` at
`ringClassNormSubgroup O`, not an independent construction, and its arithmetic is read off from
the correspondence and from ray-class reciprocity.

* Its idele-class norm group is the kernel of the ring-class quotient
  (`range_ideleClassNormMap_ringClassField`). That kernel contains the ray subgroup of the
  conductor, so the conductor modulus is admissible for it
  (`isAdmissibleModulus_ringClassField`); in particular the ring class field is unramified at
  every prime not dividing the conductor (`isUnramifiedAt_ringClassField`).
* The ray-class Artin map of the ring class field at the conductor has kernel the kernel of the
  congruence description `NumberFieldOrder.rayClassToPic : Cl_𝔣 → Pic O`, so it descends to an
  isomorphism `ringClassArtinEquiv O hK : Pic O ≃* Gal(ringClassField O hK / K)`. On idele classes
  it is the global Artin map (`ringClassArtinEquiv_ringClassIdeleQuotient`), and the degree of the
  ring class field is the order of `Pic O` (`finrank_ringClassField`).
* The ideal form of reciprocity, `ringClassArtinMap O hK`, is defined on the invertible proper
  fractional ideals of `O`; it is surjective and kills exactly the principal ones
  (`ringClassArtinMap_eq_one_iff`).
* **The splitting law.** For a prime `𝔭` of `𝓞 K` not dividing the conductor, the Artin symbol of
  the Picard class of `𝔭 ∩ O` is an arithmetic Frobenius at every prime above `𝔭`
  (`isArithFrobAt_ringClassArtinEquiv_picClass`). Hence `𝔭` splits completely in the ring class
  field exactly when it has a generator in `O` (`ncard_primesOver_ringClassField_eq_finrank_iff`).

The ring class field is asserted only for orders in quadratic fields: `ringClassField` carries the
hypothesis `Module.finrank ℚ K = 2` in its type, and so does every statement about it. The
construction itself does not consume the hypothesis; it records the classical scope of the object,
where `O = ℤ + f 𝓞 K` and the kernel of the ring-class quotient is described by ideals with a
generator congruent to a rational integer modulo `f`
(`mem_ker_ringClassIdeleQuotient_iff_of_finrank_eq_two`).

## Main definitions

* `TauCeti.ClassFieldTheory.ringClassNormSubgroup`: the kernel of the ring-class quotient, as an
  open subgroup of finite index of `C_K`.
* `TauCeti.ClassFieldTheory.ringClassField`: the ring class field of an order in a quadratic field.
* `TauCeti.ClassFieldTheory.ringClassArtinEquiv`: `Pic O ≃* Gal(ringClassField O hK / K)`.
* `TauCeti.ClassFieldTheory.ringClassArtinMap`: the Artin map on invertible proper fractional
  ideals of `O`.

## Main results

* `TauCeti.ClassFieldTheory.range_ideleClassNormMap_ringClassField`: the norm group of the ring
  class field is the kernel of the ring-class quotient.
* `TauCeti.ClassFieldTheory.isAdmissibleModulus_ringClassField`: the conductor of `O` is admissible
  for the ring class field.
* `TauCeti.ClassFieldTheory.finrank_ringClassField`: `[ringClassField O hK : K] = #Pic O`.
* `TauCeti.ClassFieldTheory.ringClassArtinMap_eq_one_iff`,
  `TauCeti.ClassFieldTheory.ringClassArtinMap_surjective`: ideal-form ring-class reciprocity.
* `TauCeti.ClassFieldTheory.isArithFrobAt_ringClassArtinEquiv_picClass`: the splitting law.
* `TauCeti.ClassFieldTheory.ncard_primesOver_ringClassField_eq_finrank_iff`: a prime not dividing
  the conductor splits completely in the ring class field exactly when it has a generator in `O`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §9.A (ring class fields and the splitting of primes).
* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields* (ring class
  fields of orders through the congruence description of the Picard group).
-/

public noncomputable section

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K] (O : NumberFieldOrder K)

/-! ### The ring-class norm subgroup and the ring class field -/

/-- The kernel of the ring-class quotient `C_K → Pic O`, as an open subgroup of finite index of the
idele class group: the source carrier of the global class-field correspondence. -/
def ringClassNormSubgroup : GlobalNormSubgroups K :=
  ⟨⟨(ringClassIdeleQuotient O).ker, isOpen_ker_ringClassIdeleQuotient O⟩, inferInstance⟩

/-- The subgroup underlying `ringClassNormSubgroup O` is the kernel of the ring-class quotient. -/
@[simp]
theorem ringClassNormSubgroup_toSubgroup :
    (ringClassNormSubgroup O).1.toSubgroup = (ringClassIdeleQuotient O).ker :=
  (rfl)

/-- **The ring class field of an order `O` in a quadratic field `K`**: the class field in `Kˢ` of
the kernel of the ring-class quotient `C_K → Pic O` under the global class-field correspondence,
that is, the unique finite abelian extension of `K` in `Kˢ` whose idele-class norm group is that
kernel (`range_ideleClassNormMap_ringClassField`). The hypothesis `_hK` records that the ring class
field is asserted only for orders in quadratic fields; the construction does not consume it. -/
def ringClassField (_hK : Module.finrank ℚ K = 2) : IntermediateField K (SeparableClosure K) :=
  classField K (globalClassField (ringClassNormSubgroup O)).1

variable (hK : Module.finrank ℚ K = 2)

/-- The ring class field of `O` is the class field of the value of the global correspondence at
the kernel of the ring-class quotient. -/
theorem ringClassField_def :
    ringClassField O hK = classField K (globalClassField (ringClassNormSubgroup O)).1 :=
  (rfl)

/-- The ring class field of `O` is a finite extension of `K`. -/
instance finiteDimensional_ringClassField : FiniteDimensional K (ringClassField O hK) :=
  finiteDimensional_classField _

/-- The ring class field of `O` is a number field. -/
instance numberField_ringClassField : NumberField (ringClassField O hK) :=
  numberField_classField _

/-- The ring class field of `O` is an abelian extension of `K`. -/
instance isAbelianGalois_ringClassField : IsAbelianGalois K (ringClassField O hK) :=
  isAbelianGalois_classField_iff.2 (globalClassField (ringClassNormSubgroup O)).2

/-- **The norm group of the ring class field is the kernel of the ring-class quotient**: an idele
class of `K` is a norm from the ring class field of `O` exactly when its image in `Pic O` is
trivial. -/
theorem range_ideleClassNormMap_ringClassField :
    (ideleClassNormMap K (ringClassField O hK) :
        IdeleClassGroup (𝓞 (ringClassField O hK)) (ringClassField O hK) →*
          IdeleClassGroup (𝓞 K) K).range =
      (ringClassIdeleQuotient O).ker :=
  (globalNormSubgroup_eq_range_classField K _).symm.trans
    (globalClassField_normSubgroup (ringClassNormSubgroup O))

/-- **The conductor of `O` is admissible for its ring class field**: the ray subgroup of the
conductor lies in the kernel of the ring-class quotient, which is the norm group. -/
theorem isAdmissibleModulus_ringClassField :
    IsAdmissibleModulus K (ringClassField O hK) O.conductorModulus :=
  isAdmissibleModulus_iff.2 <| (raySubgroup_le_ker_ringClassIdeleQuotient O).trans
    (range_ideleClassNormMap_ringClassField O hK).ge

/-- **The ring class field is unramified outside the conductor**: every prime of the ring class
field above a finite place of `K` not dividing the conductor of `O` is unramified over `K`. -/
theorem isUnramifiedAt_ringClassField {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
    (hv : v ∉ O.conductorModulus.support) (Q : Ideal (𝓞 (ringClassField O hK))) [Q.IsPrime]
    [Q.LiesOver v.asIdeal] :
    Algebra.IsUnramifiedAt (𝓞 K) Q :=
  (isAdmissibleModulus_ringClassField O hK).isUnramifiedAway v hv Q

/-! ### Ring-class reciprocity -/

/-- The ray-class Artin map of the ring class field at the conductor has the same kernel as the
congruence description `Cl_𝔣 → Pic O`: both are the image in `Cl_𝔣` of the kernel of the
ring-class quotient. -/
theorem ker_rayClassArtinMap_ringClassField :
    (rayClassArtinMap O.conductorModulus (isAdmissibleModulus_ringClassField O hK)).ker =
      O.rayClassToPic.ker := by
  rw [ker_rayClassArtinMap, range_ideleClassNormMap_ringClassField, ker_ringClassIdeleQuotient,
    Subgroup.map_comap_eq_self_of_surjective (rayClassQuotient_surjective _)]

/-- **Ring-class reciprocity**: the Artin map identifies the Picard group of `O` with the Galois
group of the ring class field. It is the ray-class Artin map of the ring class field at the
conductor, which factors through the congruence description `Cl_𝔣 → Pic O` because the two have
the same kernel (`ringClassArtinEquiv_rayClassToPic`). -/
def ringClassArtinEquiv : Pic O ≃* Gal(ringClassField O hK/K) :=
  (QuotientGroup.quotientKerEquivOfSurjective _ O.rayClassToPic_surjective).symm.trans <|
    (QuotientGroup.quotientMulEquivOfEq (ker_rayClassArtinMap_ringClassField O hK).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (rayClassArtinMap_surjective _))

/-- **Ring-class reciprocity on ray classes**: the Artin symbol of the Picard class of a ray class
of the conductor is its ray-class Artin symbol. -/
@[simp]
theorem ringClassArtinEquiv_rayClassToPic (x : RayClassGroup O.conductorModulus) :
    ringClassArtinEquiv O hK (O.rayClassToPic x) =
      rayClassArtinMap O.conductorModulus (isAdmissibleModulus_ringClassField O hK) x := by
  rw [ringClassArtinEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply,
    QuotientGroup.quotientKerEquivOfSurjective_symm_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    QuotientGroup.quotientKerEquivOfSurjective_apply_mk]

/-- **Ring-class reciprocity on idele classes**: the Artin symbol of the image in `Pic O` of an
idele class `c` is the global Artin symbol of `c` for the ring class field. -/
@[simp]
theorem ringClassArtinEquiv_ringClassIdeleQuotient (c : IdeleClassGroup (𝓞 K) K) :
    ringClassArtinEquiv O hK (ringClassIdeleQuotient O c) =
      ideleClassArtinMap K (ringClassField O hK) c := by
  rw [ringClassIdeleQuotient_apply, ringClassArtinEquiv_rayClassToPic,
    rayClassArtinMap_rayClassQuotient]

/-- **The degree of the ring class field of `O` is the order of the Picard group of `O`.** -/
theorem finrank_ringClassField :
    Module.finrank K (ringClassField O hK) = Nat.card (Pic O) := by
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr (ringClassArtinEquiv O hK).toEquiv]

/-- **The ideal form of ring-class reciprocity**: the Artin map on the invertible proper fractional
ideals of `O`, the Artin symbol of the Picard class of an ideal. -/
def ringClassArtinMap : O.invertibleProperFractionalIdeals →* Gal(ringClassField O hK/K) :=
  (ringClassArtinEquiv O hK).toMonoidHom.comp O.mkPic

/-- The ring-class Artin symbol of an invertible ideal is the Artin symbol of its Picard class. -/
@[simp]
theorem ringClassArtinMap_apply (I : O.invertibleProperFractionalIdeals) :
    ringClassArtinMap O hK I = ringClassArtinEquiv O hK (O.mkPic I) :=
  (rfl)

/-- **Ring-class reciprocity kills exactly the principal ideals**: the ring-class Artin symbol of
an invertible proper fractional ideal of `O` is trivial exactly when its Picard class is. -/
theorem ringClassArtinMap_eq_one_iff (I : O.invertibleProperFractionalIdeals) :
    ringClassArtinMap O hK I = 1 ↔ O.mkPic I = 1 := by
  rw [ringClassArtinMap_apply, MulEquiv.map_eq_one_iff]

/-- **Ring-class reciprocity is surjective**: every automorphism of the ring class field is the
Artin symbol of an invertible ideal of `O`. -/
theorem ringClassArtinMap_surjective : Function.Surjective (ringClassArtinMap O hK) :=
  (ringClassArtinEquiv O hK).surjective.comp O.mkPic_surjective

/-! ### The splitting law -/

/-- **The splitting law for the ring class field**: for a prime `𝔭` of `𝓞 K` not dividing the
conductor of `O`, the Artin symbol of the Picard class of `𝔭 ∩ O` is an arithmetic Frobenius at
every prime of the ring class field above `𝔭`. -/
theorem isArithFrobAt_ringClassArtinEquiv_picClass (I : integralIdealsPrimeTo O.conductorModulus)
    [(I : Ideal (𝓞 K)).IsMaximal] (Q : Ideal (𝓞 (ringClassField O hK))) [Q.IsPrime]
    [Q.LiesOver (I : Ideal (𝓞 K))] :
    IsArithFrobAt (𝓞 K) (ringClassArtinEquiv O hK (O.picClass I)) Q := by
  rw [← rayClassToPic_idealClass, ringClassArtinEquiv_rayClassToPic]
  exact isArithFrobAt_rayClassArtinMap_idealClass _ I Q

/-- **The splitting criterion for the ring class field**: a prime `𝔭` of `𝓞 K` not dividing the
conductor of `O` splits completely in the ring class field of `O`, that is, has
`[ringClassField O hK : K]` primes above it, exactly when it is generated by an element of `O`. -/
theorem ncard_primesOver_ringClassField_eq_finrank_iff
    (I : integralIdealsPrimeTo O.conductorModulus) [(I : Ideal (𝓞 K)).IsMaximal] :
    ((I : Ideal (𝓞 K)).primesOver (𝓞 (ringClassField O hK))).ncard =
        Module.finrank K (ringClassField O hK) ↔
      ∃ β ∈ O.toRingOfIntegers, (I : Ideal (𝓞 K)) = Ideal.span {β} := by
  -- `𝔭` is a finite place outside the support of the conductor, so it is unramified.
  have hcop := Modulus.isCoprimeTo_iff.mp (Modulus.mem_integralIdealsPrimeTo.mp I.2)
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := ⟨I, inferInstance, hcop.1⟩
  have hur : ∀ (Q : Ideal (𝓞 (ringClassField O hK))) [Q.IsPrime]
      [Q.LiesOver (I : Ideal (𝓞 K))], Algebra.IsUnramifiedAt (𝓞 K) Q := fun Q _ _ ↦
    have : Q.LiesOver v.asIdeal := ‹_›
    isUnramifiedAt_ringClassField O hK (v := v) (fun hv ↦ hcop.2 v hv dvd_rfl) Q
  -- The Artin symbol of `𝔭` is the class of the Artin symbol of the Picard class of `𝔭 ∩ O`.
  obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty ((I : Ideal (𝓞 K)).primesOver
    (𝓞 (ringClassField O hK))))
  rw [← NumberField.artinSymbol_eq_one_iff_ncard_primesOver_eq_finrank _ hur,
    NumberField.artinSymbol_eq_mk_of_isArithFrobAt _ hur Q _
      (isArithFrobAt_ringClassArtinEquiv_picClass O hK I Q),
    ConjClasses.one_eq_mk_one, ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left,
    MulEquiv.map_eq_one_iff, picClass_eq_one_iff]

end TauCeti.ClassFieldTheory
