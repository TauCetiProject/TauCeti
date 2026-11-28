/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.AdmissibleModulus.Reciprocity
public import TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.Correspondence
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Narrow.Basic

import TauCeti.FieldTheory.Galois.Abelian.Equiv
import TauCeti.FieldTheory.Galois.Restriction
import TauCeti.FieldTheory.IntermediateField.Map
import TauCeti.FieldTheory.IsSepClosed
import TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.NormLimitation

/-!
# Ray class fields and the Hilbert class field

Let `K` be a number field and `𝔪` a modulus of `K`. The ray subgroup `U_𝔪` of the idele class
group `C_K` is open and of finite index, so the global class-field correspondence attaches to it a
unique finite abelian extension of `K` inside `Kˢ` with idele-class norm group `U_𝔪`: the
**ray class field** `rayClassField 𝔪`. It is the class field of the value of `globalClassField`
at `U_𝔪`, not an independent construction, and everything below is read off from the
correspondence.

* Its norm group is the ray subgroup (`range_ideleClassNormMap_rayClassField`), so `𝔪` is
  admissible for it (`isAdmissibleModulus_rayClassField`), and it is the only finite abelian
  extension of `K` with this norm group (`fieldRange_eq_rayClassField_iff`).
* It is the **largest abelian extension in which `𝔪` is admissible**: a finite abelian extension
  `L/K` embeds in `rayClassField 𝔪` exactly when `𝔪` is admissible for `L/K`
  (`isAdmissibleModulus_iff_le_rayClassField`), that is, by
  `isAdmissibleModulus_iff_abelianConductor_dvd`, exactly when the conductor of `L/K` divides `𝔪`.
* Ray class fields grow with the modulus (`rayClassField_mono`); more precisely
  `rayClassField 𝔪 ≤ rayClassField 𝔫` exactly when `U_𝔫 ≤ U_𝔪`
  (`rayClassField_le_rayClassField_iff`).
* The ray-class Artin map of `rayClassField 𝔪` at `𝔪` is an isomorphism
  `Cl_𝔪 ≃* Gal(rayClassField 𝔪 / K)` (`rayClassArtinEquiv`), hence
  `[rayClassField 𝔪 : K] = #Cl_𝔪` (`finrank_rayClassField`).

For a totally complex base, the narrow and ordinary Hilbert class fields coincide
(`narrowHilbertClassField_eq_hilbertClassField`), since there are no real places.

The **Hilbert class field** `hilbertClassField K` is the ray class field of the trivial modulus,
and the **narrow Hilbert class field** `narrowHilbertClassField K` that of the modulus carrying
every real place and no finite place. The Artin map identifies the class group of `K` with the
Galois group of the Hilbert class field (`hilbertClassArtinEquiv`), whose degree is therefore the
class number (`finrank_hilbertClassField`). Likewise it identifies the narrow class group with the
Galois group of the narrow Hilbert class field (`narrowHilbertClassArtinEquiv`), whose degree is
the order of the narrow class group (`finrank_narrowHilbertClassField`).

The Hilbert class field is the **maximal unramified abelian extension** of `K`: a finite abelian
extension of `K` embeds in it exactly when it is unramified at every finite prime and at every
infinite place (`fieldRange_le_hilbertClassField_iff`), and it is itself unramified everywhere
(`isUnramifiedAt_hilbertClassField`, `isUnramifiedAtInfinitePlaces_hilbertClassField`). The narrow
Hilbert class field is the maximal abelian extension unramified at the finite primes, the real
places being allowed to ramify (`fieldRange_le_narrowHilbertClassField_iff`,
`isUnramifiedAt_narrowHilbertClassField`).

For any tower `K → L → Kˢ` with `L` a number field and `𝔪` a modulus of `L`, we also realize the
ray class field of `𝔪` inside `Kˢ` itself (`rayClassFieldOver K 𝔪`). It specializes to
`rayClassField 𝔪` over the base (`rayClassFieldOver_self`), is `L`-isomorphic to `rayClassField 𝔪`
(`rayClassFieldOverEquivOfAlgHom`), inherits its norm-group, admissibility, monotonicity, and
degree characterizations (`range_ideleClassNormMap_rayClassFieldOver`,
`isAdmissibleModulus_iff_le_rayClassFieldOver`, `fieldRange_eq_rayClassFieldOver_iff`,
`rayClassFieldOver_le_rayClassFieldOver_iff`, `rayClassFieldOver_mono`,
`finrank_rayClassFieldOver`), preserves unramifiedness away from `𝔪.support`
(`isUnramifiedAt_rayClassFieldOver_tower_top_of_notMem_support`,
`isUnramifiedAt_rayClassFieldOver_of_notMem_support_of_isUnramifiedAt`), and is Galois over `K`
whenever `L/K` is Galois and `𝔪` is invariant under `Gal(L/K)`-transport
(`isGalois_rayClassFieldOver_of_forall_isAdmissibleModulus`).

## Main definitions

* `TauCeti.ClassFieldTheory.rayNormSubgroup`: the ray subgroup as an open finite-index subgroup.
* `TauCeti.ClassFieldTheory.rayClassField`: the ray class field of a modulus.
* `TauCeti.ClassFieldTheory.rayClassArtinEquiv`: `Cl_𝔪 ≃* Gal(rayClassField 𝔪 / K)`.
* `TauCeti.ClassFieldTheory.hilbertClassField`, `TauCeti.ClassFieldTheory.narrowHilbertClassField`:
  the (narrow) Hilbert class field.
* `TauCeti.ClassFieldTheory.hilbertClassArtinEquiv`: `Cl_K ≃* Gal(hilbertClassField K / K)`.
* `TauCeti.ClassFieldTheory.narrowHilbertClassArtinEquiv`:
  `Cl⁺_K ≃* Gal(narrowHilbertClassField K / K)`.
* `TauCeti.ClassFieldTheory.rayClassFieldOver`: the ray class field of a modulus `𝔪` of `L`
  realized inside `SeparableClosure K`.
* `TauCeti.ClassFieldTheory.toRayClassFieldOver`,
  `TauCeti.ClassFieldTheory.algebraRayClassFieldOver`: the canonical `K`-algebra map
  `L →ₐ[K] rayClassFieldOver K 𝔪` and induced `Algebra L (rayClassFieldOver K 𝔪)` structure (with
  scalar-tower lemmas `isScalarTower_left_rayClassFieldOver` and
  `isScalarTower_right_rayClassFieldOver`).
* `TauCeti.ClassFieldTheory.rayClassFieldOverEquivOfAlgHom`: the `L`-algebra isomorphism
  `rayClassField 𝔪 ≃ₐ[L] rayClassFieldOver K 𝔪` induced by any `L`-embedding into `Kˢ`.

## Main results

* `TauCeti.ClassFieldTheory.range_ideleClassNormMap_rayClassField`: the norm group of the ray
  class field of `𝔪` is the ray subgroup of `𝔪`.
* `TauCeti.ClassFieldTheory.fieldRange_eq_rayClassField_iff`: the ray class field is the unique
  finite abelian extension with norm group the ray subgroup.
* `TauCeti.ClassFieldTheory.isAdmissibleModulus_iff_le_rayClassField`: `𝔪` is admissible for a
  finite abelian `L/K` exactly when `L` embeds in the ray class field of `𝔪`.
* `TauCeti.ClassFieldTheory.gal_rayClassField_equiv_rayClassGroup` and
  `TauCeti.ClassFieldTheory.gal_hilbertClassField_equiv_classGroup`: the Galois groups of the ray
  class field and the Hilbert class field are the ray class group and the class group.
* `TauCeti.ClassFieldTheory.finrank_rayClassField`,
  `TauCeti.ClassFieldTheory.finrank_hilbertClassField` and
  `TauCeti.ClassFieldTheory.finrank_narrowHilbertClassField`: the degrees are the order of the ray
  class group, the class number and the order of the narrow class group.
* `TauCeti.ClassFieldTheory.hilbertClassField_eq_bot_iff`: the Hilbert class field is `K` itself
  exactly when `K` has class number one.
* `TauCeti.ClassFieldTheory.exists_notMem_range_ideleClassNormMap_hilbertClassField`: when the
  class group is nontrivial, not every idele class is a norm from the Hilbert class field.
* `TauCeti.ClassFieldTheory.fieldRange_le_hilbertClassField_iff`: the Hilbert class field is the
  maximal abelian extension unramified at every finite and every infinite place.
* `TauCeti.ClassFieldTheory.fieldRange_le_narrowHilbertClassField_iff`: the narrow Hilbert class
  field is the maximal abelian extension unramified at every finite prime.
* `TauCeti.ClassFieldTheory.range_ideleClassNormMap_rayClassFieldOver`,
  `TauCeti.ClassFieldTheory.isAdmissibleModulus_iff_le_rayClassFieldOver`,
  `TauCeti.ClassFieldTheory.fieldRange_eq_rayClassFieldOver_iff`,
  `TauCeti.ClassFieldTheory.rayClassFieldOver_le_rayClassFieldOver_iff`,
  `TauCeti.ClassFieldTheory.finrank_rayClassFieldOver`: norm-group, universal-property, inclusion,
  and degree characterizations of `rayClassFieldOver K 𝔪`.
* `TauCeti.ClassFieldTheory.isUnramifiedAt_rayClassFieldOver_of_notMem_support_of_isUnramifiedAt`:
  preservation of unramifiedness away from `𝔪.support` in a tower.
* `TauCeti.ClassFieldTheory.isGalois_rayClassFieldOver_of_forall_isAdmissibleModulus`: Galoisness
  of `rayClassFieldOver K 𝔪` over `K` from `Gal(L/K)`-invariance of admissibility of `𝔪`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §6 (the ray class field).
* J. S. Milne, *Class Field Theory*, v4.03, Chapter V, §3.
-/

public noncomputable section

open IsDedekindDomain NumberField TauCeti.GlobalNumberFields
open scoped nonZeroDivisors

namespace TauCeti.ClassFieldTheory

section

variable {K : Type} [Field K] [NumberField K]

/-! ### The ray class field -/

/-- The ray subgroup of a modulus, as an open subgroup of finite index of the idele class group:
the source carrier of the global class-field correspondence. -/
def rayNormSubgroup (𝔪 : Modulus K) : GlobalNormSubgroups K :=
  ⟨⟨raySubgroup 𝔪, isOpen_raySubgroup 𝔪⟩, inferInstance⟩

/-- The subgroup underlying `rayNormSubgroup 𝔪` is the ray subgroup of `𝔪`. -/
@[simp]
theorem rayNormSubgroup_toSubgroup (𝔪 : Modulus K) :
    (rayNormSubgroup 𝔪).val.toSubgroup = raySubgroup 𝔪 :=
  (rfl)

/-- Inclusions of the bundled ray subgroups are inclusions of the ray subgroups. -/
@[simp]
theorem rayNormSubgroup_le_rayNormSubgroup_iff {𝔪 𝔫 : Modulus K} :
    rayNormSubgroup 𝔪 ≤ rayNormSubgroup 𝔫 ↔ raySubgroup 𝔪 ≤ raySubgroup 𝔫 :=
  Subtype.coe_le_coe.symm.trans OpenSubgroup.toSubgroup_le.symm

/-- **The ray class field of a modulus** `𝔪` of a number field `K`: the class field in `Kˢ` of
the ray subgroup of `𝔪` under the global class-field correspondence, that is, the unique finite
abelian extension of `K` in `Kˢ` whose idele-class norm group is the ray subgroup of `𝔪`
(`range_ideleClassNormMap_rayClassField`). -/
def rayClassField (𝔪 : Modulus K) : IntermediateField K (SeparableClosure K) :=
  classField K (globalClassField (rayNormSubgroup 𝔪)).val

/-- The ray class field of `𝔪` is the class field of the value of the global correspondence at the
ray subgroup of `𝔪`. -/
theorem rayClassField_def (𝔪 : Modulus K) :
    rayClassField 𝔪 = classField K (globalClassField (rayNormSubgroup 𝔪)).val :=
  (rfl)

variable (𝔪 : Modulus K)

/-- The ray class field of `𝔪` is a finite extension of `K`. -/
instance finiteDimensional_rayClassField : FiniteDimensional K (rayClassField 𝔪) :=
  finiteDimensional_classField _

/-- The ray class field of `𝔪` is a number field. -/
instance numberField_rayClassField : NumberField (rayClassField 𝔪) :=
  numberField_classField _

/-- The ray class field of `𝔪` is an abelian extension of `K`. -/
instance isAbelianGalois_rayClassField : IsAbelianGalois K (rayClassField 𝔪) :=
  isAbelianGalois_classField_iff.2 (globalClassField (rayNormSubgroup 𝔪)).property

/-- **The norm group of the ray class field is the ray subgroup**: `N(C_{K_𝔪}) = U_𝔪`. -/
@[simp]
theorem range_ideleClassNormMap_rayClassField :
    (ideleClassNormMap K (rayClassField 𝔪) :
        IdeleClassGroup (𝓞 (rayClassField 𝔪)) (rayClassField 𝔪) →* IdeleClassGroup (𝓞 K) K).range =
      raySubgroup 𝔪 :=
  (globalNormSubgroup_eq_range_classField K _).symm.trans
    ((globalClassField_normSubgroup (rayNormSubgroup 𝔪)).trans (rayNormSubgroup_toSubgroup 𝔪))

/-- A modulus is admissible for its own ray class field. -/
@[simp]
theorem isAdmissibleModulus_rayClassField : IsAdmissibleModulus K (rayClassField 𝔪) 𝔪 :=
  isAdmissibleModulus_iff.2 (range_ideleClassNormMap_rayClassField 𝔪).ge

variable {L : Type} [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]

/-- **The ray class field is the largest abelian extension in which `𝔪` is admissible**: for a
finite abelian extension `L/K` of number fields and any `K`-embedding `ι` of `L` into `Kˢ`, the
modulus `𝔪` is admissible for `L/K` exactly when `ι` maps `L` into the ray class field of `𝔪`. By
`isAdmissibleModulus_iff_abelianConductor_dvd`, this says that the abelian extensions of `K` with
conductor dividing `𝔪` are exactly the subextensions of the ray class field of `𝔪`. -/
theorem isAdmissibleModulus_iff_le_rayClassField (ι : L →ₐ[K] SeparableClosure K) :
    IsAdmissibleModulus K L 𝔪 ↔ ι.fieldRange ≤ rayClassField 𝔪 := by
  -- Read both norm groups as norm subgroups of layers, compare the abelian layers, and pass to
  -- their class fields, which reverses the inclusion.
  rw [isAdmissibleModulus_iff, ← globalNormSubgroup_fixingOpenNormalSubgroup,
    ← rayNormSubgroup_toSubgroup, ← globalClassField_normSubgroup,
    globalNormSubgroup_le_iff_of_isAbelian isAbelianClassFieldLayer_fixingOpenNormalSubgroup,
    ← classField_le_classField_iff, classField_fixingOpenNormalSubgroup ι, rayClassField_def]

/-- **The ray class field is characterized by its norm group**: a finite abelian extension `L/K`,
embedded in `Kˢ` by `ι`, is the ray class field of `𝔪` exactly when its idele-class norm group is
the ray subgroup of `𝔪`. -/
theorem fieldRange_eq_rayClassField_iff (ι : L →ₐ[K] SeparableClosure K) :
    ι.fieldRange = rayClassField 𝔪 ↔
      (ideleClassNormMap K L : IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range =
        raySubgroup 𝔪 := by
  -- Both sides say that the abelian layer of `L` is the value of the correspondence at `U_𝔪`.
  rw [← globalNormSubgroup_fixingOpenNormalSubgroup, ← rayNormSubgroup_toSubgroup,
    ← globalClassField_eq_iff (rayNormSubgroup 𝔪)
      ⟨_, isAbelianClassFieldLayer_fixingOpenNormalSubgroup⟩,
    ← classField_fixingOpenNormalSubgroup ι, rayClassField_def, eq_comm,
    (classField_injective K).eq_iff, Subtype.ext_iff]

variable {𝔪}

/-- **Inclusions of ray class fields are inclusions of ray subgroups**, reversed. -/
theorem rayClassField_le_rayClassField_iff {𝔫 : Modulus K} :
    rayClassField 𝔪 ≤ rayClassField 𝔫 ↔ raySubgroup 𝔫 ≤ raySubgroup 𝔪 :=
  (globalClassField_orderReversing (rayNormSubgroup 𝔫) (rayNormSubgroup 𝔪)).symm.trans
    rayNormSubgroup_le_rayNormSubgroup_iff

/-- **Ray class fields grow with the modulus**: if `𝔪 ∣ 𝔫`, the ray class field of `𝔪` lies in
that of `𝔫`. -/
theorem rayClassField_mono {𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫) : rayClassField 𝔪 ≤ rayClassField 𝔫 :=
  rayClassField_le_rayClassField_iff.2 (raySubgroup_antitone h)

/-! ### Ray-class reciprocity for the ray class field -/

variable (𝔪)

/-- **Ray-class reciprocity for the ray class field**: the ray-class Artin map
`Cl_𝔪 →* Gal(rayClassField 𝔪 / K)` is an isomorphism. -/
def rayClassArtinEquiv : RayClassGroup 𝔪 ≃* Gal(rayClassField 𝔪/K) :=
  MulEquiv.ofBijective (rayClassArtinMap 𝔪 (isAdmissibleModulus_rayClassField 𝔪))
    ⟨(MonoidHom.ker_eq_bot_iff _).1 <| by
      rw [ker_rayClassArtinMap, range_ideleClassNormMap_rayClassField, Subgroup.map_eq_bot_iff,
        ker_rayClassQuotient],
      rayClassArtinMap_surjective _⟩

/-- `rayClassArtinEquiv 𝔪` is the ray-class Artin map of the ray class field of `𝔪`. -/
@[simp]
theorem rayClassArtinEquiv_apply (x : RayClassGroup 𝔪) :
    rayClassArtinEquiv 𝔪 x = rayClassArtinMap 𝔪 (isAdmissibleModulus_rayClassField 𝔪) x :=
  (rfl)

/-- The Galois group of the ray class field of `𝔪` is the ray class group of `𝔪`, through the
inverse of `rayClassArtinEquiv 𝔪`. -/
theorem gal_rayClassField_equiv_rayClassGroup :
    Nonempty (Gal(rayClassField 𝔪/K) ≃* RayClassGroup 𝔪) :=
  ⟨(rayClassArtinEquiv 𝔪).symm⟩

/-- **The degree of the ray class field of `𝔪` is the order of the ray class group of `𝔪`.** -/
@[simp]
theorem finrank_rayClassField :
    Module.finrank K (rayClassField 𝔪) = Nat.card (RayClassGroup 𝔪) := by
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr (rayClassArtinEquiv 𝔪).toEquiv]

/-! ### The Hilbert class field and the narrow Hilbert class field -/

variable (K)

/-- **The Hilbert class field** of a number field `K`: the ray class field of the trivial modulus,
the largest abelian extension of `K` in `Kˢ` in which the trivial modulus is admissible. It is
defined for every number field, in every degree. -/
abbrev hilbertClassField : IntermediateField K (SeparableClosure K) :=
  rayClassField (Modulus.one K)

/-- **The narrow Hilbert class field** of a number field `K`: the ray class field of the modulus
`narrowModulus K`, which is trivial at the finite places and carries every real place. -/
abbrev narrowHilbertClassField : IntermediateField K (SeparableClosure K) :=
  rayClassField (narrowModulus K)

variable {K} in
/-- The Hilbert class field lies in every ray class field. -/
theorem hilbertClassField_le_rayClassField : hilbertClassField K ≤ rayClassField 𝔪 :=
  rayClassField_mono (Modulus.one_dvd 𝔪)

/-- The Hilbert class field lies in the narrow Hilbert class field. -/
theorem hilbertClassField_le_narrowHilbertClassField :
    hilbertClassField K ≤ narrowHilbertClassField K :=
  hilbertClassField_le_rayClassField _

/-- Over a totally complex number field, the narrow and ordinary Hilbert class fields coincide:
there are no real places at which a narrow class field could allow extra ramification. -/
@[simp]
theorem narrowHilbertClassField_eq_hilbertClassField [IsTotallyComplex K] :
    narrowHilbertClassField K = hilbertClassField K :=
  congrArg rayClassField (narrowModulus_eq_one K)

/-- **Reciprocity for the Hilbert class field**: the Artin map identifies the class group of `K`
with the Galois group of the Hilbert class field: `rayClassArtinEquiv` at the trivial modulus, read
on the class group through `oneEquivClassGroup`. -/
def hilbertClassArtinEquiv : ClassGroup (𝓞 K) ≃* Gal(hilbertClassField K/K) :=
  oneEquivClassGroup.symm.trans (rayClassArtinEquiv (Modulus.one K))

variable {K} in
/-- On the class group, `hilbertClassArtinEquiv` is the ray-class Artin map of the trivial
modulus. -/
@[simp]
theorem hilbertClassArtinEquiv_oneEquivClassGroup (x : RayClassGroup (Modulus.one K)) :
    hilbertClassArtinEquiv K (oneEquivClassGroup x) = rayClassArtinEquiv (Modulus.one K) x := by
  rw [hilbertClassArtinEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

variable {K} in
/-- The Artin symbol of the class of a fractional ideal `I` in the Hilbert class field is the
ray-class Artin symbol of `I` at the trivial modulus. -/
@[simp]
theorem hilbertClassArtinEquiv_mk (I : idealsPrimeTo (Modulus.one K)) :
    hilbertClassArtinEquiv K (ClassGroup.mk K (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) =
      rayClassArtinEquiv (Modulus.one K) (rayClassMk (Modulus.one K) I) := by
  rw [← oneEquivClassGroup_rayClassMk, hilbertClassArtinEquiv_oneEquivClassGroup]

variable {K} in
/-- The inverse of `hilbertClassArtinEquiv` is the inverse of the ray-class Artin isomorphism at
the trivial modulus, followed by `oneEquivClassGroup`. -/
@[simp]
theorem hilbertClassArtinEquiv_symm_apply (σ : Gal(hilbertClassField K/K)) :
    (hilbertClassArtinEquiv K).symm σ =
      oneEquivClassGroup ((rayClassArtinEquiv (Modulus.one K)).symm σ) :=
  (rfl)

/-- The Galois group of the Hilbert class field is the class group, through the inverse of
`hilbertClassArtinEquiv K`. -/
theorem gal_hilbertClassField_equiv_classGroup :
    Nonempty (Gal(hilbertClassField K/K) ≃* ClassGroup (𝓞 K)) :=
  ⟨(hilbertClassArtinEquiv K).symm⟩

/-- **The degree of the Hilbert class field is the class number.** -/
@[simp high]
theorem finrank_hilbertClassField : Module.finrank K (hilbertClassField K) = classNumber K := by
  rw [← IsGalois.card_aut_eq_finrank, ← Nat.card_congr (hilbertClassArtinEquiv K).toEquiv,
    classNumber, Nat.card_eq_fintype_card]

/-- **The Hilbert class field is trivial exactly in class number one.** -/
theorem hilbertClassField_eq_bot_iff : hilbertClassField K = ⊥ ↔ classNumber K = 1 := by
  rw [← IntermediateField.finrank_eq_one_iff, finrank_hilbertClassField]

/-- **Not every idele class is a norm from a nontrivial Hilbert class field.** The norm group of
the Hilbert class field is the trivial-modulus ray subgroup, the kernel of the quotient onto the
class group, so any nontrivial ideal class lifts to an idele class outside it. -/
theorem exists_notMem_range_ideleClassNormMap_hilbertClassField
    [Nontrivial (ClassGroup (𝓞 K))] :
    ∃ c : IdeleClassGroup (𝓞 K) K,
      c ∉ (ideleClassNormMap K (hilbertClassField K) :
        IdeleClassGroup (𝓞 (hilbertClassField K)) (hilbertClassField K) →*
          IdeleClassGroup (𝓞 K) K).range := by
  rw [range_ideleClassNormMap_rayClassField, ← ker_rayClassQuotient]
  obtain ⟨x, hx⟩ := exists_ne (1 : ClassGroup (𝓞 K))
  obtain ⟨c, hc⟩ := rayClassQuotient_surjective _ (oneEquivClassGroup.symm x)
  refine ⟨c, fun h => hx ?_⟩
  rw [MonoidHom.mem_ker, hc] at h
  simpa using congrArg oneEquivClassGroup h

/-- **Reciprocity for the narrow Hilbert class field**: the Artin map identifies the narrow class
group of `K` with the Galois group of the narrow Hilbert class field: `rayClassArtinEquiv` at the
narrow modulus, read on the narrow class group through `narrowEquivNarrowClassGroup`. -/
def narrowHilbertClassArtinEquiv : NarrowClassGroup K ≃* Gal(narrowHilbertClassField K/K) :=
  narrowEquivNarrowClassGroup.symm.trans (rayClassArtinEquiv (narrowModulus K))

variable {K} in
/-- On the narrow class group, `narrowHilbertClassArtinEquiv` is the ray-class Artin map of the
narrow modulus. -/
@[simp]
theorem narrowHilbertClassArtinEquiv_narrowEquivNarrowClassGroup
    (x : RayClassGroup (narrowModulus K)) :
    narrowHilbertClassArtinEquiv K (narrowEquivNarrowClassGroup x) =
      rayClassArtinEquiv (narrowModulus K) x := by
  rw [narrowHilbertClassArtinEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

variable {K} in
/-- The Artin symbol of the narrow class of a fractional ideal `I` in the narrow Hilbert class
field is the ray-class Artin symbol of `I` at the narrow modulus. -/
@[simp]
theorem narrowHilbertClassArtinEquiv_mk (I : idealsPrimeTo (narrowModulus K)) :
    narrowHilbertClassArtinEquiv K (NarrowClassGroup.mk (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) =
      rayClassArtinEquiv (narrowModulus K) (rayClassMk (narrowModulus K) I) := by
  rw [← narrowEquivNarrowClassGroup_rayClassMk,
    narrowHilbertClassArtinEquiv_narrowEquivNarrowClassGroup]

variable {K} in
/-- The inverse of `narrowHilbertClassArtinEquiv` is the inverse of the ray-class Artin
isomorphism at the narrow modulus, followed by `narrowEquivNarrowClassGroup`. -/
@[simp]
theorem narrowHilbertClassArtinEquiv_symm_apply (σ : Gal(narrowHilbertClassField K/K)) :
    (narrowHilbertClassArtinEquiv K).symm σ =
      narrowEquivNarrowClassGroup ((rayClassArtinEquiv (narrowModulus K)).symm σ) :=
  (rfl)

/-- **The degree of the narrow Hilbert class field is the order of the narrow class group.** -/
@[simp high]
theorem finrank_narrowHilbertClassField :
    Module.finrank K (narrowHilbertClassField K) = Nat.card (NarrowClassGroup K) := by
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr (narrowHilbertClassArtinEquiv K).toEquiv]

/-! ### The Hilbert class fields are the maximal unramified abelian extensions -/

/-- **The Hilbert class field is unramified at every finite prime**: every prime of the Hilbert
class field of `K` is unramified over `𝓞 K`. -/
theorem isUnramifiedAt_hilbertClassField (w : HeightOneSpectrum (𝓞 (hilbertClassField K))) :
    Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
  (isAdmissibleModulus_one_iff.1 (isAdmissibleModulus_rayClassField _)).1 w

/-- **The Hilbert class field is unramified at the infinite places**: every real place of `K`
stays real in the Hilbert class field. -/
instance isUnramifiedAtInfinitePlaces_hilbertClassField :
    IsUnramifiedAtInfinitePlaces K (hilbertClassField K) :=
  (isAdmissibleModulus_one_iff.1 (isAdmissibleModulus_rayClassField _)).2

variable {K} in
/-- **The Hilbert class field is the maximal unramified abelian extension**: a finite abelian
extension `L/K` of number fields, embedded in `Kˢ` by `ι`, lies in the Hilbert class field of `K`
exactly when it is unramified at every finite prime and at every infinite place. -/
theorem fieldRange_le_hilbertClassField_iff (ι : L →ₐ[K] SeparableClosure K) :
    ι.fieldRange ≤ hilbertClassField K ↔
      (∀ w : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) ∧
        IsUnramifiedAtInfinitePlaces K L := by
  rw [← isAdmissibleModulus_iff_le_rayClassField, isAdmissibleModulus_one_iff]

variable {K} in
omit [NumberField L] in
/-- An everywhere-unramified abelian extension whose degree equals the class number is the
Hilbert class field, for every embedding into the separable closure of the base. -/
theorem fieldRange_eq_hilbertClassField_of_unramified_of_finrank_eq_classNumber
    (ι : L →ₐ[K] SeparableClosure K)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    (hinf : IsUnramifiedAtInfinitePlaces K L) (hdeg : Module.finrank K L = classNumber K) :
    ι.fieldRange = hilbertClassField K := by
  have hpos : 0 < Module.finrank K L := hdeg ▸ NumberField.classNumber_pos K
  have : Module.Finite K L := Module.finite_of_finrank_pos hpos
  have : NumberField L := NumberField.of_module_finite K L
  apply IntermediateField.eq_of_le_of_finrank_eq
  · exact (fieldRange_le_hilbertClassField_iff ι).2 ⟨hfin, hinf⟩
  · rw [← ι.equivFieldRange.toLinearEquiv.finrank_eq, finrank_hilbertClassField, hdeg]

/-- **The narrow Hilbert class field is unramified at every finite prime**: every prime of the
narrow Hilbert class field of `K` is unramified over `𝓞 K`. -/
theorem isUnramifiedAt_narrowHilbertClassField
    (w : HeightOneSpectrum (𝓞 (narrowHilbertClassField K))) :
    Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
  isAdmissibleModulus_narrowModulus_iff.1 (isAdmissibleModulus_rayClassField _) w

variable {K} in
/-- **The narrow Hilbert class field is the maximal abelian extension unramified at the finite
primes**: a finite abelian extension `L/K` of number fields, embedded in `Kˢ` by `ι`, lies in the
narrow Hilbert class field of `K` exactly when it is unramified at every finite prime. The real
places of `K` may ramify. -/
theorem fieldRange_le_narrowHilbertClassField_iff (ι : L →ₐ[K] SeparableClosure K) :
    ι.fieldRange ≤ narrowHilbertClassField K ↔
      ∀ w : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := by
  rw [← isAdmissibleModulus_iff_le_rayClassField, isAdmissibleModulus_narrowModulus_iff]

end

/-! ### Relative ray class fields in the separable closure of the base -/

section RelativeClassFields

variable (K : Type) [Field K]
  {L : Type} [Field L] [NumberField L] [Algebra K L]
  [Algebra L (SeparableClosure K)] [IsScalarTower K L (SeparableClosure K)]
  (𝔪 : Modulus L)

/-- **The ray class field of a modulus `𝔪` of `L`, realized in `SeparableClosure K`**: the normal
closure over `L` of `rayClassField 𝔪` inside `SeparableClosure K`, viewed as an intermediate field
over `K`. Because `rayClassField 𝔪` is normal over `L`, every `L`-embedding of `rayClassField 𝔪`
into `SeparableClosure K` has this field as its image (`rayClassFieldOver_eq_fieldRange`). -/
def rayClassFieldOver : IntermediateField K (SeparableClosure K) :=
  (IntermediateField.normalClosure L (rayClassField 𝔪) (SeparableClosure K)).restrictScalars K

/-- Every `L`-embedding of `rayClassField 𝔪` into `SeparableClosure K` has image
`rayClassFieldOver K 𝔪`. -/
theorem rayClassFieldOver_eq_fieldRange (ι : rayClassField 𝔪 →ₐ[L] SeparableClosure K) :
    rayClassFieldOver K 𝔪 = ι.fieldRange.restrictScalars K :=
  congrArg (IntermediateField.restrictScalars K) (IntermediateField.normalClosure_eq_fieldRange ι)

/-- Over the base field `K` itself, `rayClassFieldOver K 𝔪` is `rayClassField 𝔪`. -/
@[simp]
theorem rayClassFieldOver_self {K : Type} [Field K] [NumberField K] (𝔪 : Modulus K) :
    rayClassFieldOver K 𝔪 = rayClassField 𝔪 := by
  rw [rayClassFieldOver_eq_fieldRange K 𝔪 (rayClassField 𝔪).val, IntermediateField.fieldRange_val,
    IntermediateField.restrictScalars_self]

/-- The image of `L` in `SeparableClosure K` lies inside `rayClassFieldOver K 𝔪`. -/
theorem algebraMap_mem_rayClassFieldOver (a : L) :
    algebraMap L (SeparableClosure K) a ∈ rayClassFieldOver K 𝔪 :=
  (IntermediateField.normalClosure L (rayClassField 𝔪) (SeparableClosure K)).algebraMap_mem a

/-- When `E` is an intermediate field of `SeparableClosure K / K`, `E` lies inside
`rayClassFieldOver K 𝔪` for every modulus `𝔪` of `E`. -/
theorem le_rayClassFieldOver {K : Type} [Field K]
    (E : IntermediateField K (SeparableClosure K)) [NumberField E] (𝔪 : Modulus E) :
    E ≤ rayClassFieldOver K 𝔪 :=
  fun x hx ↦ algebraMap_mem_rayClassFieldOver K 𝔪 ⟨x, hx⟩

/-- Canonical `K`-algebra homomorphism `L →ₐ[K] rayClassFieldOver K 𝔪`. -/
def toRayClassFieldOver : L →ₐ[K] rayClassFieldOver K 𝔪 :=
  (IsScalarTower.toAlgHom K L (SeparableClosure K)).codRestrict
    (rayClassFieldOver K 𝔪).toSubalgebra (algebraMap_mem_rayClassFieldOver K 𝔪)

/-- In `SeparableClosure K`, `toRayClassFieldOver K 𝔪` is `algebraMap L (SeparableClosure K)`. -/
@[simp]
theorem coe_toRayClassFieldOver_apply (a : L) :
    (toRayClassFieldOver K 𝔪 a : SeparableClosure K) = algebraMap L (SeparableClosure K) a :=
  (rfl)

/-- Canonical `L`-algebra structure on `rayClassFieldOver K 𝔪`, induced by
`toRayClassFieldOver K 𝔪`. Activate this as a local instance together with
`isScalarTower_left_rayClassFieldOver` and `isScalarTower_right_rayClassFieldOver` when no
compatible `Algebra L (rayClassFieldOver K 𝔪)` instance is already in scope (it is not a global
instance because for `L = K` it would compete with `IntermediateField.algebra`). -/
@[instance_reducible]
def algebraRayClassFieldOver : Algebra L (rayClassFieldOver K 𝔪) :=
  (toRayClassFieldOver K 𝔪).toRingHom.toAlgebra

section
attribute [local instance] algebraRayClassFieldOver

/-- `K → L → rayClassFieldOver K 𝔪` is a scalar tower for `algebraRayClassFieldOver K 𝔪`. -/
theorem isScalarTower_left_rayClassFieldOver :
    IsScalarTower K L (rayClassFieldOver K 𝔪) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ Subtype.ext <|
    (IntermediateField.coe_algebraMap_apply _ x).trans
      (IsScalarTower.algebraMap_apply K L (SeparableClosure K) x)

/-- `L → rayClassFieldOver K 𝔪 → SeparableClosure K` is a scalar tower for
`algebraRayClassFieldOver K 𝔪`. -/
theorem isScalarTower_right_rayClassFieldOver :
    IsScalarTower L (rayClassFieldOver K 𝔪) (SeparableClosure K) :=
  IsScalarTower.of_algebraMap_eq fun x ↦
    (IntermediateField.algebraMap_apply _ (toRayClassFieldOver K 𝔪 x)).symm

end

/-- Any `L`-embedding `ι : rayClassField 𝔪 →ₐ[L] SeparableClosure K` restricts to an `L`-algebra
isomorphism `rayClassField 𝔪 ≃ₐ[L] rayClassFieldOver K 𝔪`, for any compatible `L`-algebra
structure on `rayClassFieldOver K 𝔪`. -/
def rayClassFieldOverEquivOfAlgHom (ι : rayClassField 𝔪 →ₐ[L] SeparableClosure K)
    [Algebra L (rayClassFieldOver K 𝔪)]
    [IsScalarTower L (rayClassFieldOver K 𝔪) (SeparableClosure K)] :
    rayClassField 𝔪 ≃ₐ[L] rayClassFieldOver K 𝔪 :=
  AlgEquiv.ofRingEquiv
    (f := ι.equivFieldRange.toRingEquiv.trans <|
      (IntermediateField.restrictScalarsAlgEquiv K ι.fieldRange).symm.toRingEquiv.trans
        (IntermediateField.equivOfEq (rayClassFieldOver_eq_fieldRange K 𝔪 ι).symm).toRingEquiv)
    fun a ↦ Subtype.ext <| by
      simp [← IntermediateField.algebraMap_apply (rayClassFieldOver K 𝔪),
        ← IsScalarTower.algebraMap_apply L (rayClassFieldOver K 𝔪) (SeparableClosure K)]

/-- In `SeparableClosure K`, `rayClassFieldOverEquivOfAlgHom K 𝔪 ι` acts as `ι`. -/
@[simp]
theorem coe_rayClassFieldOverEquivOfAlgHom_apply (ι : rayClassField 𝔪 →ₐ[L] SeparableClosure K)
    [Algebra L (rayClassFieldOver K 𝔪)]
    [IsScalarTower L (rayClassFieldOver K 𝔪) (SeparableClosure K)] (x : rayClassField 𝔪) :
    (rayClassFieldOverEquivOfAlgHom K 𝔪 ι x : SeparableClosure K) = ι x := by
  simp [rayClassFieldOverEquivOfAlgHom]

/-- `rayClassFieldOver K 𝔪` is `L`-isomorphic to `rayClassField 𝔪`. -/
theorem nonempty_algEquiv_rayClassFieldOver [Algebra L (rayClassFieldOver K 𝔪)]
    [IsScalarTower L (rayClassFieldOver K 𝔪) (SeparableClosure K)] :
    Nonempty (rayClassField 𝔪 ≃ₐ[L] rayClassFieldOver K 𝔪) :=
  ⟨rayClassFieldOverEquivOfAlgHom K 𝔪 IsSepClosed.lift⟩

/-- `rayClassFieldOver K 𝔪` is an abelian Galois extension of `L`. -/
instance isAbelianGalois_rayClassFieldOver [Algebra L (rayClassFieldOver K 𝔪)]
    [IsScalarTower L (rayClassFieldOver K 𝔪) (SeparableClosure K)] :
    IsAbelianGalois L (rayClassFieldOver K 𝔪) :=
  IsAbelianGalois.of_algHom (rayClassFieldOverEquivOfAlgHom K 𝔪 IsSepClosed.lift).symm.toAlgHom

/-- `rayClassFieldOver K 𝔪` is a number field. -/
instance numberField_rayClassFieldOver : NumberField (rayClassFieldOver K 𝔪) :=
  have : NumberField (IntermediateField.normalClosure L (rayClassField 𝔪) (SeparableClosure K)) :=
    .of_module_finite L _
  .of_ringEquiv _ _ (IntermediateField.restrictScalarsAlgEquiv K _).symm.toRingEquiv

/-- `rayClassFieldOver K 𝔪` is finite-dimensional over `K`. -/
instance finiteDimensional_rayClassFieldOver :
    FiniteDimensional K (rayClassFieldOver K 𝔪) := by
  have := (algebraMap K L).charZero
  exact Module.Finite.of_restrictScalars_finite ℚ K (rayClassFieldOver K 𝔪)

/-- **The norm group of `rayClassFieldOver K 𝔪` over `L` is `raySubgroup 𝔪`.** -/
@[simp]
theorem range_ideleClassNormMap_rayClassFieldOver
    [Algebra L (rayClassFieldOver K 𝔪)]
    [IsScalarTower L (rayClassFieldOver K 𝔪) (SeparableClosure K)] :
    (ideleClassNormMap L (rayClassFieldOver K 𝔪) :
        IdeleClassGroup (𝓞 (rayClassFieldOver K 𝔪)) (rayClassFieldOver K 𝔪) →*
          IdeleClassGroup (𝓞 L) L).range = raySubgroup 𝔪 :=
  (range_ideleClassNormMap_eq_of_algEquiv
    (rayClassFieldOverEquivOfAlgHom K 𝔪 IsSepClosed.lift).symm).trans
    (range_ideleClassNormMap_rayClassField 𝔪)

/-- A modulus `𝔪` of `L` is admissible for `rayClassFieldOver K 𝔪 / L`. -/
@[simp]
theorem isAdmissibleModulus_rayClassFieldOver
    [Algebra L (rayClassFieldOver K 𝔪)]
    [IsScalarTower L (rayClassFieldOver K 𝔪) (SeparableClosure K)] :
    IsAdmissibleModulus L (rayClassFieldOver K 𝔪) 𝔪 :=
  isAdmissibleModulus_iff.2 (range_ideleClassNormMap_rayClassFieldOver K 𝔪).ge

/-- **The degree of `rayClassFieldOver K 𝔪` over `L` is the order of `RayClassGroup 𝔪`.** -/
@[simp]
theorem finrank_rayClassFieldOver
    [Algebra L (rayClassFieldOver K 𝔪)]
    [IsScalarTower L (rayClassFieldOver K 𝔪) (SeparableClosure K)] :
    Module.finrank L (rayClassFieldOver K 𝔪) = Nat.card (RayClassGroup 𝔪) :=
  (rayClassFieldOverEquivOfAlgHom K 𝔪 IsSepClosed.lift).symm.toLinearEquiv.finrank_eq.trans
    (finrank_rayClassField 𝔪)

/-- An `L`-algebra isomorphism `e : SeparableClosure K ≃ₐ[L] SeparableClosure L` identifies
`rayClassFieldOver K 𝔪` with `(rayClassField 𝔪).map e.symm.toAlgHom`. -/
private theorem rayClassFieldOver_eq_map
    (e : SeparableClosure K ≃ₐ[L] SeparableClosure L) :
    rayClassFieldOver K 𝔪 = ((rayClassField 𝔪).map e.symm.toAlgHom).restrictScalars K := by
  rw [rayClassFieldOver_eq_fieldRange K 𝔪 (e.symm.toAlgHom.comp (rayClassField 𝔪).val),
    IntermediateField.fieldRange_comp_val]

private theorem restrictScalars_le_rayClassFieldOver_iff
    (F : IntermediateField L (SeparableClosure K))
    (e : SeparableClosure K ≃ₐ[L] SeparableClosure L) :
    F.restrictScalars K ≤ rayClassFieldOver K 𝔪 ↔ F.map e.toAlgHom ≤ rayClassField 𝔪 := by
  rw [rayClassFieldOver_eq_map K 𝔪 e, IntermediateField.restrictScalars_le_iff K]
  exact ⟨fun h ↦ (IntermediateField.map_mono e.toAlgHom h).trans_eq
      (IntermediateField.map_map_symm e (rayClassField 𝔪)),
    fun h ↦ (IntermediateField.map_symm_map e F).symm.trans_le
      (IntermediateField.map_mono e.symm.toAlgHom h)⟩

private theorem rayClassFieldOver_le_restrictScalars_iff
    (F : IntermediateField L (SeparableClosure K))
    (e : SeparableClosure K ≃ₐ[L] SeparableClosure L) :
    rayClassFieldOver K 𝔪 ≤ F.restrictScalars K ↔ rayClassField 𝔪 ≤ F.map e.toAlgHom := by
  rw [rayClassFieldOver_eq_map K 𝔪 e, IntermediateField.restrictScalars_le_iff K]
  exact ⟨fun h ↦ (IntermediateField.map_map_symm e (rayClassField 𝔪)).symm.trans_le
      (IntermediateField.map_mono e.toAlgHom h),
    fun h ↦ (IntermediateField.map_mono e.symm.toAlgHom h).trans_eq
      (IntermediateField.map_symm_map e F)⟩

/-- **Universal property of `rayClassFieldOver K 𝔪`**: for a finite abelian extension `M/L` and any
`L`-embedding `ι : M →ₐ[L] SeparableClosure K`, `𝔪` is admissible for `M/L` if and only if the
image of `ι` lies in `rayClassFieldOver K 𝔪`. -/
theorem isAdmissibleModulus_iff_le_rayClassFieldOver
    {M : Type} [Field M] [NumberField M] [Algebra L M] [IsAbelianGalois L M]
    (ι : M →ₐ[L] SeparableClosure K) :
    IsAdmissibleModulus L M 𝔪 ↔ ι.fieldRange.restrictScalars K ≤ rayClassFieldOver K 𝔪 := by
  have := TauCeti.isSepClosure_tower_top K L (SeparableClosure K)
  let e := IsSepClosure.equiv L (SeparableClosure K) (SeparableClosure L)
  have hrange : (e.toAlgHom.comp ι).fieldRange = ι.fieldRange.map e.toAlgHom := by ext; simp
  rw [isAdmissibleModulus_iff_le_rayClassField 𝔪 (e.toAlgHom.comp ι), hrange,
    restrictScalars_le_rayClassFieldOver_iff K 𝔪 _ e]

/-- **Norm-group characterization of `rayClassFieldOver K 𝔪`**: a finite abelian extension `M/L`
embedded in `SeparableClosure K` by `ι` has image `rayClassFieldOver K 𝔪` if and only if its
idele-class norm group over `L` is `raySubgroup 𝔪`. -/
theorem fieldRange_eq_rayClassFieldOver_iff
    {M : Type} [Field M] [NumberField M] [Algebra L M] [IsAbelianGalois L M]
    (ι : M →ₐ[L] SeparableClosure K) :
    ι.fieldRange.restrictScalars K = rayClassFieldOver K 𝔪 ↔
      (ideleClassNormMap L M : IdeleClassGroup (𝓞 M) M →* IdeleClassGroup (𝓞 L) L).range =
        raySubgroup 𝔪 := by
  have := TauCeti.isSepClosure_tower_top K L (SeparableClosure K)
  let e := IsSepClosure.equiv L (SeparableClosure K) (SeparableClosure L)
  have hrange : (e.toAlgHom.comp ι).fieldRange = ι.fieldRange.map e.toAlgHom := by ext; simp
  rw [← fieldRange_eq_rayClassField_iff 𝔪 (e.toAlgHom.comp ι), hrange, le_antisymm_iff,
    le_antisymm_iff, restrictScalars_le_rayClassFieldOver_iff K 𝔪 _ e,
    rayClassFieldOver_le_restrictScalars_iff K 𝔪 _ e]

variable {K 𝔪} in
/-- **Inclusions of relative ray class fields are inclusions of ray subgroups, reversed.** -/
theorem rayClassFieldOver_le_rayClassFieldOver_iff {𝔫 : Modulus L} :
    rayClassFieldOver K 𝔪 ≤ rayClassFieldOver K 𝔫 ↔ raySubgroup 𝔫 ≤ raySubgroup 𝔪 := by
  have := TauCeti.isSepClosure_tower_top K L (SeparableClosure K)
  let e := IsSepClosure.equiv L (SeparableClosure K) (SeparableClosure L)
  rw [rayClassFieldOver_eq_map K 𝔪 e, restrictScalars_le_rayClassFieldOver_iff K 𝔫 _ e,
    IntermediateField.map_map_symm e (rayClassField 𝔪), rayClassField_le_rayClassField_iff]

variable {K 𝔪} in
/-- **Relative ray class fields grow with the modulus**: if `𝔪 ∣ 𝔫`, then
`rayClassFieldOver K 𝔪 ≤ rayClassFieldOver K 𝔫`. -/
theorem rayClassFieldOver_mono {𝔫 : Modulus L} (h : 𝔪 ∣ 𝔫) :
    rayClassFieldOver K 𝔪 ≤ rayClassFieldOver K 𝔫 :=
  rayClassFieldOver_le_rayClassFieldOver_iff.2 (raySubgroup_antitone h)

/-- Every prime `w` of `rayClassFieldOver K 𝔪` lying over a prime of `𝓞 L` outside `𝔪.support` is
unramified over `𝓞 L`. -/
theorem isUnramifiedAt_rayClassFieldOver_tower_top_of_notMem_support
    [Algebra L (rayClassFieldOver K 𝔪)]
    [IsScalarTower L (rayClassFieldOver K 𝔪) (SeparableClosure K)]
    {w : HeightOneSpectrum (𝓞 (rayClassFieldOver K 𝔪))}
    (hw : w.under (𝓞 L) ∉ 𝔪.support) :
    Algebra.IsUnramifiedAt (𝓞 L) w.asIdeal :=
  (isAdmissibleModulus_rayClassFieldOver K 𝔪).isUnramifiedAt_of_notMem_support hw w

/-- If `w` is a prime of `rayClassFieldOver K 𝔪` whose restriction `w.under (𝓞 L)` avoids
`𝔪.support` and is unramified over `𝓞 K`, then `w` is unramified over `𝓞 K`. -/
theorem isUnramifiedAt_rayClassFieldOver_of_notMem_support_of_isUnramifiedAt
    [Algebra L (rayClassFieldOver K 𝔪)]
    [IsScalarTower L (rayClassFieldOver K 𝔪) (SeparableClosure K)]
    {w : HeightOneSpectrum (𝓞 (rayClassFieldOver K 𝔪))}
    (hw : w.under (𝓞 L) ∉ 𝔪.support)
    (hL : Algebra.IsUnramifiedAt (𝓞 K) (w.under (𝓞 L)).asIdeal) :
    Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := by
  have : IsScalarTower K L (rayClassFieldOver K 𝔪) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ Subtype.ext <|
      (IntermediateField.coe_algebraMap_apply _ x).trans <|
        (IsScalarTower.algebraMap_apply K L (SeparableClosure K) x).trans <|
          (IsScalarTower.algebraMap_apply L (rayClassFieldOver K 𝔪) (SeparableClosure K) _).trans
            (IntermediateField.algebraMap_apply _ _)
  have : Algebra.IsUnramifiedAt (𝓞 L) w.asIdeal :=
    isUnramifiedAt_rayClassFieldOver_tower_top_of_notMem_support K 𝔪 hw
  exact Algebra.IsUnramifiedAt.comp (w.under (𝓞 L)).asIdeal w.asIdeal

/-- For `L/K` Galois and `σ ∈ Gal(Kˢ/K)`, the image of `rayClassFieldOver K 𝔪` under `σ` carries a
compatible `L`-algebra structure and is isomorphic to `rayClassField 𝔪` compatibly with `σ`'s
restriction to `L`. -/
private theorem exists_ringEquiv_map_rayClassFieldOver [IsGalois K L]
    (σ : Gal(SeparableClosure K/K)) :
    ∃ (_ : Algebra L ((rayClassFieldOver K 𝔪).map
        (σ : SeparableClosure K →ₐ[K] SeparableClosure K))),
      ∃ (_ : IsScalarTower L
          ((rayClassFieldOver K 𝔪).map (σ : SeparableClosure K →ₐ[K] SeparableClosure K))
          (SeparableClosure K)),
        ∃ g : rayClassField 𝔪 ≃+*
            (rayClassFieldOver K 𝔪).map (σ : SeparableClosure K →ₐ[K] SeparableClosure K),
          (algebraMap L
              ((rayClassFieldOver K 𝔪).map
                (σ : SeparableClosure K →ₐ[K] SeparableClosure K))).comp
            ((σ.restrictNormal L).toRingEquiv : L →+* L) =
            (g : rayClassField 𝔪 →+* _).comp (algebraMap L (rayClassField 𝔪)) := by
  let _ := algebraRayClassFieldOver K 𝔪
  have := isScalarTower_right_rayClassFieldOver K 𝔪
  let H := rayClassFieldOver K 𝔪
  let Hσ := H.map (σ : SeparableClosure K →ₐ[K] SeparableClosure K)
  have hmem (a : L) : algebraMap L (SeparableClosure K) a ∈ Hσ := by
    let b := (σ.restrictNormal L).symm a
    have hσb : (σ : SeparableClosure K →ₐ[K] SeparableClosure K)
        (algebraMap L (SeparableClosure K) b) ∈ Hσ :=
      (H.map_mem_map _).mpr (algebraMap_mem_rayClassFieldOver K 𝔪 b)
    rwa [AlgEquiv.coe_toAlgHom, ← AlgEquiv.restrictNormal_commutes σ L b,
      AlgEquiv.apply_symm_apply] at hσb
  let φL : L →+* Hσ := (algebraMap L (SeparableClosure K)).codRestrict Hσ hmem
  let instAlg : Algebra L Hσ := φL.toAlgebra
  have instTower : IsScalarTower L Hσ (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      ((IntermediateField.algebraMap_apply Hσ (φL x)).trans
        (RingHom.codRestrict_apply _ Hσ hmem x)).symm
  let ι : rayClassField 𝔪 →ₐ[L] SeparableClosure K := IsSepClosed.lift
  let g : rayClassField 𝔪 ≃+* Hσ :=
    (rayClassFieldOverEquivOfAlgHom K 𝔪 ι).toRingEquiv.trans
      (H.equivMap (σ : SeparableClosure K →ₐ[K] SeparableClosure K)).toRingEquiv
  refine ⟨instAlg, instTower, g, RingHom.ext fun a ↦ Subtype.ext ?_⟩
  have hEq : ((algebraMap L Hσ (σ.restrictNormal L a) : Hσ) : SeparableClosure K) =
      σ ((algebraMap L H a : H) : SeparableClosure K) :=
    ((IntermediateField.algebraMap_apply Hσ _).symm.trans <|
      (IsScalarTower.algebraMap_apply L Hσ (SeparableClosure K) _).symm.trans
        (AlgEquiv.restrictNormal_commutes σ L a)).trans <|
      congrArg σ <|
        (IsScalarTower.algebraMap_apply L H (SeparableClosure K) a).trans
          (IntermediateField.algebraMap_apply H _)
  simpa [g] using hEq

/-- If `L/K` is Galois and `𝔪` remains admissible for every finite abelian extension `M/L` linked
to `rayClassField 𝔪 / L` by a `K`-algebra automorphism of `L`, then `rayClassFieldOver K 𝔪` is
Galois over `K`. -/
theorem isGalois_rayClassFieldOver_of_forall_isAdmissibleModulus [IsGalois K L]
    (hadm : ∀ {M : Type} [Field M] [NumberField M] [Algebra L M] [IsAbelianGalois L M]
      (f : Gal(L/K)) (g : rayClassField 𝔪 ≃+* M),
      (algebraMap L M).comp (f.toRingEquiv : L →+* L) =
        (g : rayClassField 𝔪 →+* M).comp (algebraMap L (rayClassField 𝔪)) →
      IsAdmissibleModulus L M 𝔪) :
    IsGalois K (rayClassFieldOver K 𝔪) := by
  have : Normal K (rayClassFieldOver K 𝔪) := by
    refine IntermediateField.normal_iff_forall_map_le'.mpr fun σ ↦ ?_
    obtain ⟨instAlg, instTower, g, hcomp⟩ := exists_ringEquiv_map_rayClassFieldOver K 𝔪 σ
    let Hσ := (rayClassFieldOver K 𝔪).map (σ : SeparableClosure K →ₐ[K] SeparableClosure K)
    have : NumberField Hσ := .of_ringEquiv _ _ g
    have : IsAbelianGalois L Hσ :=
      IsAbelianGalois.of_equiv_equiv (σ.restrictNormal L).toRingEquiv g hcomp
    have hle := (isAdmissibleModulus_iff_le_rayClassFieldOver K 𝔪
      (IsScalarTower.toAlgHom L Hσ (SeparableClosure K))).mp
        (hadm (σ.restrictNormal L) g hcomp)
    intro x hx
    exact hle ⟨⟨x, hx⟩, IntermediateField.algebraMap_apply Hσ ⟨x, hx⟩⟩
  exact {}

end RelativeClassFields

end TauCeti.ClassFieldTheory
