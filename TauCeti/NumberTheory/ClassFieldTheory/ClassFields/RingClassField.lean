/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RingClassQuotient
public import TauCeti.NumberTheory.ClassFieldTheory.Global.AdmissibleModulus.Reciprocity
public import TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.Correspondence

/-!
# The ring class field of an order

Let `O` be an order in a number field `K`, with conductor `𝔣`. The kernel of the idelic
ring-class quotient `ringClassIdeleQuotient O : C_K → Pic O` is an open subgroup of finite index
of the idele class group, so the global class-field correspondence attaches to it a unique finite
abelian extension of `K` inside `Kˢ` with that idele-class norm group: the **ring class field**
`ringClassField O`. It is the class field of the value of `globalClassField` at this subgroup, not
an independent construction, and everything below is read off from the correspondence and from
ray-class reciprocity.

* Its norm group is the kernel of the ring-class quotient
  (`range_ideleClassNormMap_ringClassField`). That kernel contains the ray subgroup of `𝔣`, so the
  conductor modulus of `O` is admissible for the ring class field
  (`isAdmissibleModulus_ringClassField`).
* The ray-class Artin map of the ring class field at `𝔣` therefore exists; it is surjective, and
  its kernel is the image of the norm group in `Cl_𝔣`, which is the kernel of the congruence
  description `Cl_𝔣 → Pic O` (`ker_rayClassArtinMap_ringClassField`). Both maps out of `Cl_𝔣`
  being surjective with the same kernel, the Artin map descends to an isomorphism
  `ringClassArtinEquiv O : Pic O ≃* Gal(ringClassField O / K)`. On idele classes it is the global
  Artin map (`ringClassArtinEquiv_ringClassIdeleQuotient`), and it obeys the **splitting law**: the
  Picard class of the contraction to `O` of a prime `𝔭` of `𝓞 K` prime to `𝔣` maps to an
  arithmetic Frobenius at every prime above `𝔭` (`isArithFrobAt_ringClassArtinEquiv_picClass`).
  Hence `[ringClassField O : K] = #Pic O` (`finrank_ringClassField`).
* Composed with the Picard class map, it is the ideal form of reciprocity on invertible fractional
  ideals of `O`, `ringClassArtinMap O`, which is surjective and kills exactly the principal ideals
  (`ringClassArtinMap_eq_one_iff`).

No hypothesis on the degree of `K` is needed: the congruence description
`NumberFieldOrder.rayClassToPic` of `Pic O` as a quotient of `Cl_𝔣` holds for every order
(Kopp–Lagarias). In a quadratic field, where `O = ℤ + f 𝓞 K`, the norm group is the classical
one, cut out by ideals with a generator congruent to a rational integer modulo `f`
(`mem_ker_ringClassIdeleQuotient_iff_of_finrank_eq_two`).

## Main definitions

* `TauCeti.ClassFieldTheory.ringClassNormSubgroup`: the kernel of the ring-class quotient as an
  open finite-index subgroup of `C_K`.
* `TauCeti.ClassFieldTheory.ringClassField`: the ring class field of an order.
* `TauCeti.ClassFieldTheory.ringClassArtinEquiv`: `Pic O ≃* Gal(ringClassField O / K)`.
* `TauCeti.ClassFieldTheory.ringClassArtinMap`: reciprocity on invertible fractional ideals.

## Main results

* `TauCeti.ClassFieldTheory.range_ideleClassNormMap_ringClassField`: the norm group of the ring
  class field is the kernel of the ring-class quotient.
* `TauCeti.ClassFieldTheory.isAdmissibleModulus_ringClassField`: the conductor modulus of `O` is
  admissible for its ring class field.
* `TauCeti.ClassFieldTheory.ringClassArtinEquiv_ringClassIdeleQuotient`: on idele classes the
  isomorphism is the global Artin map.
* `TauCeti.ClassFieldTheory.isArithFrobAt_ringClassArtinEquiv_picClass`: the splitting law.
* `TauCeti.ClassFieldTheory.finrank_ringClassField`: the degree is the order of `Pic O`.
* `TauCeti.ClassFieldTheory.ringClassArtinMap_eq_one_iff`: the ideal form of reciprocity kills
  exactly the principal ideals.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §9, Theorem 9.18.
* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields*, Theorem 1.1.
-/

public noncomputable section

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K] (O : NumberFieldOrder K)

/-! ### The ring class field -/

/-- The kernel of the ring-class quotient of an order, as an open subgroup of finite index of the
idele class group: the source carrier of the global class-field correspondence. -/
def ringClassNormSubgroup : GlobalNormSubgroups K :=
  ⟨⟨(ringClassIdeleQuotient O).ker, isOpen_ker_ringClassIdeleQuotient O⟩, inferInstance⟩

/-- The subgroup underlying `ringClassNormSubgroup O` is the kernel of the ring-class quotient. -/
@[simp]
theorem ringClassNormSubgroup_toSubgroup :
    (ringClassNormSubgroup O).1.toSubgroup = (ringClassIdeleQuotient O).ker :=
  (rfl)

/-- **The ring class field of an order** `O` of a number field `K`: the class field in `Kˢ` of the
kernel of the ring-class quotient `C_K → Pic O` under the global class-field correspondence, that
is, the unique finite abelian extension of `K` in `Kˢ` whose idele-class norm group is that kernel
(`range_ideleClassNormMap_ringClassField`). -/
def ringClassField : IntermediateField K (SeparableClosure K) :=
  classField K (globalClassField (ringClassNormSubgroup O)).1

/-- The ring class field of `O` is the class field of the value of the global correspondence at
the kernel of the ring-class quotient. -/
theorem ringClassField_def :
    ringClassField O = classField K (globalClassField (ringClassNormSubgroup O)).1 :=
  (rfl)

/-- The ring class field of `O` is a finite extension of `K`. -/
instance finiteDimensional_ringClassField : FiniteDimensional K (ringClassField O) :=
  finiteDimensional_classField _

/-- The ring class field of `O` is a number field. -/
instance numberField_ringClassField : NumberField (ringClassField O) :=
  numberField_classField _

/-- The ring class field of `O` is an abelian extension of `K`. -/
instance isAbelianGalois_ringClassField : IsAbelianGalois K (ringClassField O) :=
  isAbelianGalois_classField_iff.2 (globalClassField (ringClassNormSubgroup O)).2

/-- **The norm group of the ring class field is the kernel of the ring-class quotient**: an idele
class of `K` is a norm from the ring class field of `O` exactly when its ray class modulo the
conductor is the class of an ideal generated by an element of `O`
(`mem_ker_ringClassIdeleQuotient_iff`). -/
theorem range_ideleClassNormMap_ringClassField :
    (ideleClassNormMap K (ringClassField O) :
        IdeleClassGroup (𝓞 (ringClassField O)) (ringClassField O) →*
          IdeleClassGroup (𝓞 K) K).range =
      (ringClassIdeleQuotient O).ker :=
  (globalNormSubgroup_eq_range_classField K _).symm.trans
    (globalClassField_normSubgroup (ringClassNormSubgroup O))

/-- The conductor modulus of an order is admissible for its ring class field: the ray subgroup of
the conductor lies in the kernel of the ring-class quotient. -/
theorem isAdmissibleModulus_ringClassField :
    IsAdmissibleModulus K (ringClassField O) O.conductorModulus :=
  isAdmissibleModulus_iff.2 <|
    (raySubgroup_le_ker_ringClassIdeleQuotient O).trans
      (range_ideleClassNormMap_ringClassField O).ge

/-! ### Reciprocity for the ring class field -/

/-- **The kernel of ray-class reciprocity for the ring class field** is the kernel of the
congruence description `Cl_𝔣 → Pic O`: it is the image in `Cl_𝔣` of the norm group, the preimage
of that kernel under the surjective ray class map. -/
theorem ker_rayClassArtinMap_ringClassField :
    (rayClassArtinMap O.conductorModulus (isAdmissibleModulus_ringClassField O)).ker =
      O.rayClassToPic.ker := by
  rw [ker_rayClassArtinMap, range_ideleClassNormMap_ringClassField, ker_ringClassIdeleQuotient,
    Subgroup.map_comap_eq_self_of_surjective (rayClassQuotient_surjective _)]

/-- **Reciprocity for the ring class field**: the Artin map identifies the Picard group of `O`
with the Galois group of the ring class field of `O`. It is the ray-class Artin map of the ring
class field at the conductor, which factors through the congruence description `Cl_𝔣 → Pic O`
because the two surjections out of `Cl_𝔣` have the same kernel
(`ker_rayClassArtinMap_ringClassField`). -/
def ringClassArtinEquiv : Pic O ≃* Gal(ringClassField O/K) :=
  MulEquiv.ofBijective
    (O.rayClassToPic.liftOfSurjective O.rayClassToPic_surjective
      ⟨rayClassArtinMap O.conductorModulus (isAdmissibleModulus_ringClassField O),
        (ker_rayClassArtinMap_ringClassField O).ge⟩)
    ⟨(injective_iff_map_eq_one _).2 fun y hy ↦ by
      obtain ⟨x, rfl⟩ := O.rayClassToPic_surjective y
      rw [MonoidHom.liftOfRightInverse_comp_apply] at hy
      rw [← MonoidHom.mem_ker, ← ker_rayClassArtinMap_ringClassField O]
      exact MonoidHom.mem_ker.2 hy,
    fun σ ↦ by
      obtain ⟨x, rfl⟩ := rayClassArtinMap_surjective (isAdmissibleModulus_ringClassField O) σ
      exact ⟨O.rayClassToPic x, MonoidHom.liftOfRightInverse_comp_apply _ _
        (Function.rightInverse_surjInv O.rayClassToPic_surjective) _ x⟩⟩

/-- **`ringClassArtinEquiv` factors the ray-class Artin map**: the image of the Picard class of a
ray class `x` of the conductor is the ray-class Artin symbol of `x`. -/
@[simp]
theorem ringClassArtinEquiv_rayClassToPic (x : RayClassGroup O.conductorModulus) :
    ringClassArtinEquiv O (O.rayClassToPic x) =
      rayClassArtinMap O.conductorModulus (isAdmissibleModulus_ringClassField O) x :=
  MonoidHom.liftOfRightInverse_comp_apply _ _
    (Function.rightInverse_surjInv O.rayClassToPic_surjective) _ x

/-- **On idele classes, ring-class reciprocity is the global Artin map**: the image of the
ring-class quotient of `c ∈ C_K` is the global Artin symbol of `c` in the ring class field. -/
@[simp]
theorem ringClassArtinEquiv_ringClassIdeleQuotient (c : IdeleClassGroup (𝓞 K) K) :
    ringClassArtinEquiv O (ringClassIdeleQuotient O c) =
      ideleClassArtinMap K (ringClassField O) c := by
  rw [ringClassIdeleQuotient_apply, ringClassArtinEquiv_rayClassToPic,
    rayClassArtinMap_rayClassQuotient]

/-- On the Picard class of the contraction of an ideal `J` of `𝓞 K` prime to the conductor,
ring-class reciprocity is the ray-class Artin symbol of `J`. -/
@[simp]
theorem ringClassArtinEquiv_picClass (J : integralIdealsPrimeTo O.conductorModulus) :
    ringClassArtinEquiv O (O.picClass J) =
      rayClassArtinMap O.conductorModulus (isAdmissibleModulus_ringClassField O)
        (idealClass O.conductorModulus J) := by
  rw [← rayClassToPic_idealClass, ringClassArtinEquiv_rayClassToPic]

/-- **The splitting law for the ring class field**: for a prime `𝔭` of `𝓞 K` prime to the
conductor of `O`, the image under ring-class reciprocity of the Picard class of `𝔭 ∩ O` is an
arithmetic Frobenius at every prime of the ring class field above `𝔭`. -/
theorem isArithFrobAt_ringClassArtinEquiv_picClass
    (J : integralIdealsPrimeTo O.conductorModulus) [(J : Ideal (𝓞 K)).IsMaximal]
    (Q : Ideal (𝓞 (ringClassField O))) [Q.IsPrime] [Q.LiesOver (J : Ideal (𝓞 K))] :
    IsArithFrobAt (𝓞 K) (ringClassArtinEquiv O (O.picClass J)) Q := by
  rw [ringClassArtinEquiv_picClass]
  exact isArithFrobAt_rayClassArtinMap_idealClass _ J Q

/-- **The degree of the ring class field of `O` is the order of the Picard group of `O`.** -/
theorem finrank_ringClassField :
    Module.finrank K (ringClassField O) = Nat.card (Pic O) := by
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr (ringClassArtinEquiv O).toEquiv]

/-! ### Reciprocity on invertible ideals -/

/-- **The ideal form of ring-class reciprocity**: an invertible fractional ideal of `O` maps to the
image under `ringClassArtinEquiv` of its Picard class. -/
def ringClassArtinMap : O.invertibleProperFractionalIdeals →* Gal(ringClassField O/K) :=
  (ringClassArtinEquiv O).toMonoidHom.comp O.mkPic

/-- The ideal form of ring-class reciprocity is `ringClassArtinEquiv` on Picard classes. -/
@[simp]
theorem ringClassArtinMap_apply (I : O.invertibleProperFractionalIdeals) :
    ringClassArtinMap O I = ringClassArtinEquiv O (O.mkPic I) :=
  (rfl)

/-- **Ring-class reciprocity kills exactly the principal ideals**: an invertible fractional ideal
of `O` has trivial Artin symbol in the ring class field exactly when it is principal. -/
theorem ringClassArtinMap_eq_one_iff (I : O.invertibleProperFractionalIdeals) :
    ringClassArtinMap O I = 1 ↔ (I : Submodule O.toSubalgebra K).IsPrincipal := by
  rw [ringClassArtinMap_apply, MulEquiv.map_eq_one_iff, ClassGroup.mk_eq_one_iff]

/-- The ideal form of ring-class reciprocity is surjective. -/
theorem ringClassArtinMap_surjective : Function.Surjective (ringClassArtinMap O) :=
  (ringClassArtinEquiv O).surjective.comp O.mkPic_surjective

end TauCeti.ClassFieldTheory
